import FleetArchimedeanNumericalCertificate

/-! Semantic checkpoints for numerical certificates. Each checked interval has
literal rational endpoints; subsequent steps use its theorem, without reducing
the computation which produced it again. -/

namespace FleetMicroPointCertificate
open FleetRationalInterval FleetElementaryIntervalCertificate
open FleetDigammaEfficientCertificate FleetEfficientArchimedeanCertificate

theorem exp_seed {x : ℚ} {b : Box} (hx : |x| ≤ 1)
    (hl : b.lo ≤ expPolynomial 12 x - expRemainder 12 x)
    (hu : expPolynomial 12 x + expRemainder 12 x ≤ b.hi) :
    Contains b (Real.exp (x : ℝ)) :=
  exp_small (by norm_num) hx hl hu

theorem exp_step {x y : ℚ} {a b : Box} (hy : y = 2*x)
    (ha : Contains a (Real.exp (x : ℝ))) (hpos : 0 ≤ a.lo)
    (hl : b.lo ≤ a.lo^2) (hu : a.hi^2 ≤ b.hi) :
    Contains b (Real.exp (y : ℝ)) := by
  have h := exp_double ha hpos hl hu
  rw [hy]
  simpa only [Rat.cast_mul, Rat.cast_ofNat] using h

theorem sample_from_parts {q u x y : ℚ} {e p l b : Box}
    (hx : x = -u^2) (hy : y = q/2+u)
    (he : Contains e (Real.exp (x : ℝ)))
    (hp : Contains p (efficientPsiApprox 32 (y : ℝ)))
    (hl : Contains l (Real.log Real.pi))
    (hlo : b.lo ≤ (mul e (sub p l)).lo)
    (hhi : (mul e (sub p l)).hi ≤ b.hi) :
    Contains b (efficientIntegrand 32 (q : ℝ) (u : ℝ)) := by
  have h := enlarge (mul_contains he (sub_contains hp hl)) hlo hhi
  rw [hx, hy] at h
  simp only [Rat.cast_neg, Rat.cast_pow, Rat.cast_add, Rat.cast_div,
    Rat.cast_ofNat] at h
  unfold efficientIntegrand efficientWeightApprox
  convert h using 1 <;> congr 2 <;> ring

end FleetMicroPointCertificate
