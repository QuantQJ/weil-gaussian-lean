import FleetGaussianFiniteReduction

/-!
# Exact real closed forms of the finite Gaussian arithmetic target

At width one, the two pole evaluations combine into
`2 * sqrt pi * exp (1/16 - q^2/4) * cos (q/4)`. Pairing the retained prime
summands at centers `q` and `-q` gives the real expression
`2 * (Λ n / sqrt n) * exp (-(log n)^2) * cos (q * log n)`.

These identities are proved for the exact Fourier transforms, complex powers,
and finite sums used by `FleetGaussianFiniteReduction.finiteRHS`. They remove
complex arithmetic from the retained target, but do not numerically enclose
its real elementary functions or its remaining finite archimedean integral.
No residual bound or stage-feasibility claim is asserted here.
-/

noncomputable section
namespace FleetGaussianFiniteClosedForm
open GaussianTest Complex
open scoped ArithmeticFunction

/-- Conjugate exponential phases combine to a real cosine expression. -/
lemma exp_pair (a t : ℝ) :
    Complex.exp ((a : ℂ)+(t : ℂ)*I) + Complex.exp ((a : ℂ)-(t : ℂ)*I) =
      ((2*Real.exp a*Real.cos t : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.exp_re, Complex.exp_im, Complex.cos_ofReal_re]; ring

/-- Exact width-one closed form for both pole evaluations together. -/
lemma pole_pair (q : ℝ) :
    FleetFullLineFourier.h (gauss 1 q) (I/2) +
      FleetFullLineFourier.h (gauss 1 q) (-I/2) =
      ((2*Real.sqrt Real.pi*Real.exp (1/16-q^2/4)*Real.cos (q/4) : ℝ) : ℂ) := by
  rw [FleetGaussianDictionaryMember.h_gauss_eq (by norm_num : (0 : ℝ) < 1),
    FleetGaussianDictionaryMember.h_gauss_eq (by norm_num : (0 : ℝ) < 1)]
  simp only [div_one, ofReal_one, mul_one]
  have hp : -(I/2-(q : ℂ))^2/4 =
      ((1/16-q^2/4 : ℝ) : ℂ)+((q/4 : ℝ) : ℂ)*I := by
    push_cast
    ring_nf
    simp [I_sq]
    ring
  have hm : -(-I/2-(q : ℂ))^2/4 =
      ((1/16-q^2/4 : ℝ) : ℂ)-((q/4 : ℝ) : ℂ)*I := by
    push_cast
    ring_nf
    simp [I_sq]
    ring
  rw [hp, hm, ← mul_add, exp_pair]
  push_cast
  ring

/-- The existing complex power at a natural base equals the real reciprocal
square root, including the totalized value at zero. -/
lemma nat_cpow_neg_half (n : ℕ) :
    (n : ℂ)^(-(1/2) : ℂ) = (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) := by
  have hh : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) = (n : ℂ)^(1/2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  rw [Complex.cpow_neg, ← hh, ← Complex.ofReal_inv]

/-- Opposite Gaussian modulations pair to a real cosine. -/
lemma gauss_pair (q u : ℝ) :
    gauss 1 q u + gauss 1 (-q) u =
      ((2*Real.exp (-u^2)*Real.cos (q*u) : ℝ) : ℂ) := by
  unfold gauss
  simp only [Complex.ofReal_one]
  have hp : -(1 : ℂ)*(u : ℂ)^2-I*(q : ℂ)*(u : ℂ) =
      ((-u^2 : ℝ) : ℂ)-((q*u : ℝ) : ℂ)*I := by push_cast; ring
  have hm : -(1 : ℂ)*(u : ℂ)^2-I*((-q : ℝ) : ℂ)*(u : ℂ) =
      ((-u^2 : ℝ) : ℂ)+((q*u : ℝ) : ℂ)*I := by push_cast; ring
  rw [hp, hm, add_comm, exp_pair]

/-- Exact real closed form of an original and reflected prime summand. -/
lemma paired_prime_term (q : ℝ) (n : ℕ) :
    FleetPrimeFunctionalBound.term (gauss 1 q) n +
      FleetPrimeFunctionalBound.term (gauss 1 (-q)) n =
      ((2*((Λ n)/Real.sqrt (n : ℝ))*Real.exp (-(Real.log n)^2)*
        Real.cos (q*Real.log n) : ℝ) : ℂ) := by
  unfold FleetPrimeFunctionalBound.term
  rw [← mul_add, gauss_pair, nat_cpow_neg_half]
  push_cast
  ring

/-- The real summand before the factor two from pairing opposite centers. -/
def primeTermReal (q : ℝ) (n : ℕ) : ℝ :=
  (Λ n)/Real.sqrt (n : ℝ)*Real.exp (-(Real.log n)^2)*Real.cos (q*Real.log n)

/-- The retained real summand at zero vanishes. -/
lemma primeTermReal_zero (q : ℝ) : primeTermReal q 0 = 0 := by
  simp [primeTermReal]

/-- The retained real summand at one vanishes. -/
lemma primeTermReal_one (q : ℝ) : primeTermReal q 1 = 0 := by
  simp [primeTermReal]

/-- The original complex pair at zero also vanishes. -/
lemma paired_prime_term_zero (q : ℝ) :
    FleetPrimeFunctionalBound.term (gauss 1 q) 0 +
      FleetPrimeFunctionalBound.term (gauss 1 (-q)) 0 = 0 := by
  simp [FleetPrimeFunctionalBound.term]

/-- The original complex pair at one also vanishes. -/
lemma paired_prime_term_one (q : ℝ) :
    FleetPrimeFunctionalBound.term (gauss 1 q) 1 +
      FleetPrimeFunctionalBound.term (gauss 1 (-q)) 1 = 0 := by
  simp [FleetPrimeFunctionalBound.term]

/-- The paired finite prime sum has the exact real closed form for every
natural cutoff; all integer locations through `N` are retained. -/
theorem paired_partialSum (q : ℝ) (N : ℕ) :
    FleetGaussianPrimeTailCertificate.partialSum N q +
      FleetGaussianPrimeTailCertificate.partialSum N (-q) =
      ((2*∑ n ∈ Finset.range (N+1), primeTermReal q n : ℝ) : ℂ) := by
  unfold FleetGaussianPrimeTailCertificate.partialSum
  rw [← Finset.sum_add_distrib]
  simp_rw [paired_prime_term]
  rw [← Complex.ofReal_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  unfold primeTermReal
  ring

/-- The exact real finite target: the pole pair plus the retained archimedean
integral, minus twice the retained real prime sum through 1000. -/
def finiteRHSReal (q : ℝ) : ℝ :=
  2*Real.sqrt Real.pi*Real.exp (1/16-q^2/4)*Real.cos (q/4) +
  (1/Real.sqrt Real.pi)*(∫ u : ℝ in Set.Ioc (-12) 12,
    FleetArchimedeanTailCertificate.integrand q u) -
  2*∑ n ∈ Finset.range (1000+1), primeTermReal q n

/-- Exact agreement with the complex finite arithmetic target already used
in the proved infinite-tail reduction. -/
theorem finiteRHS_eq_real (q : ℝ) :
    FleetGaussianFiniteReduction.finiteRHS q = (finiteRHSReal q : ℂ) := by
  unfold FleetGaussianFiniteReduction.finiteRHS
  rw [pole_pair, sub_sub, paired_partialSum]
  unfold FleetGaussianFiniteReduction.finiteArchimedean finiteRHSReal
  push_cast
  rfl

end FleetGaussianFiniteClosedForm
