import FleetEfficientArchimedeanCertificate
import Mathlib

/-! Explicit derivatives and uniform curvature bounds for the finite
archimedean integrand. -/

noncomputable section
open Complex Finset Real
open FleetDigammaIntervalCertificate FleetDigammaEfficientCertificate

namespace FleetEfficientArchimedeanDerivatives

def point (k : ℕ) (z : ℂ) : ℂ := (k:ℂ) + 1/4 + I*z

lemma point_real_re (k : ℕ) (y : ℝ) : (point k y).re = (k:ℝ)+1/4 := by
  simp [point]

lemma point_ne_zero (k : ℕ) (y : ℝ) : point k y ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  rw [point_real_re] at h'
  simp only [Complex.zero_re] at h'
  have hk : (0:ℝ) ≤ k := by positivity
  linarith

lemma hasDerivAt_point (k : ℕ) (z : ℂ) : HasDerivAt (point k) I z := by
  change HasDerivAt (fun w : ℂ => (k:ℂ)+1/4+I*w) I z
  convert ((hasDerivAt_id z).const_mul I).const_add ((k:ℂ)+1/4) using 1 <;> simp

def complexApprox (N : ℕ) (z : ℂ) : ℂ :=
  Complex.log (point N z) - (point N z)⁻¹/2 -
    ∑ k ∈ range N, (point k z)⁻¹

def complexFirst (N : ℕ) (z : ℂ) : ℂ :=
  I * ((point N z)⁻¹ + ((point N z)⁻¹)^2/2 +
    ∑ k ∈ range N, ((point k z)⁻¹)^2)

def complexSecond (N : ℕ) (z : ℂ) : ℂ :=
  ((point N z)⁻¹)^2 + ((point N z)⁻¹)^3 +
    2 * ∑ k ∈ range N, ((point k z)⁻¹)^3

lemma complexApprox_re (N : ℕ) (y : ℝ) :
    (complexApprox N y).re = efficientPsiApprox N y := by
  rw [← center_eq_efficientPsiApprox]
  unfold complexApprox center asymptotic
  have hp (k : ℕ) : point k y = quarterPoint y + (k:ℂ) := by
    unfold point quarterPoint
    ring
  simp only [hp, Complex.sub_re, Complex.div_ofNat_re, Complex.re_sum]

lemma hasDerivAt_complexApprox (N : ℕ) (y : ℝ) :
    HasDerivAt (complexApprox N) (complexFirst N y) (y:ℂ) := by
  have hp := hasDerivAt_point N (y:ℂ)
  have hs : point N y ∈ Complex.slitPlane := by
    exact Or.inl (by rw [point_real_re]; positivity)
  have hh := ((hp.clog hs).sub ((hp.inv (point_ne_zero N y)).div_const 2)).sub
    (HasDerivAt.fun_sum (u := range N) (fun k _ =>
      (hasDerivAt_point k (y:ℂ)).inv (point_ne_zero k y)))
  convert hh using 1
  · rfl
  unfold complexFirst
  simp only [div_eq_mul_inv, inv_pow, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

lemma hasDerivAt_complexFirst (N : ℕ) (y : ℝ) :
    HasDerivAt (complexFirst N) (complexSecond N y) (y:ℂ) := by
  have hp (k : ℕ) := (hasDerivAt_point k (y:ℂ)).inv (point_ne_zero k y)
  have hh := (((hp N).add (((hp N).pow 2).div_const 2)).add
    (HasDerivAt.fun_sum (u := range N) (fun k _ => (hp k).pow 2))).const_mul I
  convert hh using 1
  · rfl
  unfold complexSecond
  simp only [div_eq_mul_inv, Nat.cast_ofNat, pow_one, Finset.mul_sum, Pi.inv_apply, Pi.pow_apply]
  ring_nf
  simp only [Complex.I_sq, mul_neg, neg_neg, mul_one, sub_neg_eq_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [inv_pow]
  ring_nf
  simp [Complex.I_sq]

def first (N : ℕ) (y : ℝ) : ℝ := (complexFirst N y).re
def second (N : ℕ) (y : ℝ) : ℝ := (complexSecond N y).re

lemma hasDerivAt_efficientPsiApprox (N : ℕ) (y : ℝ) :
    HasDerivAt (efficientPsiApprox N) (first N y) y := by
  simpa only [complexApprox_re, first] using (hasDerivAt_complexApprox N y).real_of_complex

lemma hasDerivAt_first (N : ℕ) (y : ℝ) :
    HasDerivAt (first N) (second N y) y :=
  (hasDerivAt_complexFirst N y).real_of_complex

lemma norm_point_inv_le (k : ℕ) (y : ℝ) :
    ‖(point k y)⁻¹‖ ≤ 1/((k:ℝ)+1/4) := by
  rw [norm_inv, one_div]
  apply inv_anti₀ (by positivity)
  rw [← point_real_re k y]
  exact Complex.re_le_norm _

lemma norm_point_inv_le_four (k : ℕ) (y : ℝ) :
    ‖(point k y)⁻¹‖ ≤ 4 := by
  refine (norm_point_inv_le k y).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hk : (0:ℝ) ≤ k := by positivity
  linarith

lemma norm_point_inv_le_one (N : ℕ) (hN : 2 ≤ N) (y : ℝ) :
    ‖(point N y)⁻¹‖ ≤ 1 := by
  refine (norm_point_inv_le N y).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN
  linarith

lemma sum_recip_sq_le (N : ℕ) :
    (∑ k ∈ range N, 1/((k:ℝ)+1/4)^2) ≤ 20-5/((N:ℝ)+1/4) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ]
    have hn : 0 < (N:ℝ)+1/4 := by positivity
    have hn1 : 0 < (N:ℝ)+1/4+1 := by positivity
    have hs : 1/((N:ℝ)+1/4)^2 ≤
        5/((N:ℝ)+1/4)-5/((N:ℝ)+1/4+1) := by
      have he : 5/((N:ℝ)+1/4)-5/((N:ℝ)+1/4+1) =
          5/(((N:ℝ)+1/4)*((N:ℝ)+1/4+1)) := by field_simp; ring
      rw [he, div_le_div_iff₀ (sq_pos_of_pos hn) (mul_pos hn hn1)]
      have hn0 : (0:ℝ) ≤ N := by positivity
      nlinarith
    push_cast
    rw [show (N:ℝ)+1+1/4 = (N:ℝ)+1/4+1 by ring]
    linarith

lemma sum_norm_inv_sq_le (N : ℕ) (y : ℝ) :
    (∑ k ∈ range N, ‖(point k y)⁻¹‖^2) ≤ 20 := by
  calc
    _ ≤ ∑ k ∈ range N, 1/((k:ℝ)+1/4)^2 := by
      apply sum_le_sum
      intro k hk
      calc
        _ ≤ (1/((k:ℝ)+1/4))^2 := by
          gcongr
          exact norm_point_inv_le k y
        _ = _ := by simp only [div_pow, one_pow]
    _ ≤ 20-5/((N:ℝ)+1/4) := sum_recip_sq_le N
    _ ≤ 20 := sub_le_self _ (by positivity)

lemma sum_norm_inv_cube_le (N : ℕ) (y : ℝ) :
    (∑ k ∈ range N, ‖(point k y)⁻¹‖^3) ≤ 80 := by
  calc
    _ ≤ ∑ k ∈ range N, 4*‖(point k y)⁻¹‖^2 := by
      apply sum_le_sum
      intro k hk
      have h := mul_le_mul_of_nonneg_right (norm_point_inv_le_four k y)
        (sq_nonneg ‖(point k y)⁻¹‖)
      nlinarith
    _ = 4*(∑ k ∈ range N, ‖(point k y)⁻¹‖^2) := by rw [mul_sum]
    _ ≤ 80 := by linarith [sum_norm_inv_sq_le N y]

theorem abs_first_le (N : ℕ) (hN : 2 ≤ N) (y : ℝ) : |first N y| ≤ 22 := by
  have hi := norm_point_inv_le_one N hN y
  have hi0 : 0 ≤ ‖(point N y)⁻¹‖ := norm_nonneg _
  have hi2 : ‖(point N y)⁻¹‖^2 ≤ 1 := by nlinarith
  have hs : ‖∑ k ∈ range N, ((point k y)⁻¹)^2‖ ≤ 20 := by
    refine (norm_sum_le _ _).trans ?_
    simpa only [norm_pow] using sum_norm_inv_sq_le N y
  calc
    _ ≤ ‖complexFirst N y‖ := Complex.abs_re_le_norm _
    _ = ‖(point N y)⁻¹ + ((point N y)⁻¹)^2/2 +
        ∑ k ∈ range N, ((point k y)⁻¹)^2‖ := by
      simp [complexFirst]
    _ ≤ ‖(point N y)⁻¹‖ + ‖((point N y)⁻¹)^2/2‖ +
        ‖∑ k ∈ range N, ((point k y)⁻¹)^2‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ 22 := by
      simp only [norm_div, norm_pow, Complex.norm_ofNat]
      linarith

theorem abs_second_le (N : ℕ) (hN : 2 ≤ N) (y : ℝ) : |second N y| ≤ 162 := by
  have hi := norm_point_inv_le_one N hN y
  have hi0 : 0 ≤ ‖(point N y)⁻¹‖ := norm_nonneg _
  have hi2 : ‖(point N y)⁻¹‖^2 ≤ 1 := by nlinarith
  have hi3 : ‖(point N y)⁻¹‖^3 ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hi2 hi0]
  have hs : ‖∑ k ∈ range N, ((point k y)⁻¹)^3‖ ≤ 80 := by
    refine (norm_sum_le _ _).trans ?_
    simpa only [norm_pow] using sum_norm_inv_cube_le N y
  calc
    _ ≤ ‖complexSecond N y‖ := Complex.abs_re_le_norm _
    _ ≤ ‖((point N y)⁻¹)^2‖ + ‖((point N y)⁻¹)^3‖ +
        ‖2*(∑ k ∈ range N, ((point k y)⁻¹)^3)‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ 162 := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
      linarith

lemma norm_psi_le_forty_five {y : ℝ} (hy : |y| ≤ 62) :
    ‖FleetGammaKernel.psi (quarterPoint y)‖ ≤ 45 := by
  have hz : 0 < (quarterPoint y).re := by rw [quarterPoint_re]; norm_num
  have h := FleetDigammaGrowth.norm_logDerivative_le
    (z := quarterPoint y) (δ := 1/4) (by norm_num) (by norm_num)
    (by rw [quarterPoint_re])
  rw [← FleetGammaIdentification.digamma_eq_series _ hz] at h
  change ‖FleetGammaKernel.psi (quarterPoint y)‖ ≤ _ at h
  have hγ : |Real.eulerMascheroniConstant| ≤ 1 := by
    rw [_root_.abs_of_nonneg (by linarith [Real.one_half_lt_eulerMascheroniConstant])]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hlog : Real.log (2+‖quarterPoint y-1‖) ≤ 7 := by
    calc
      _ ≤ Real.log ((2:ℝ)^7) := Real.log_le_log (by positivity) (by
        rw [show (2:ℝ)^7 = 128 by norm_num]
        linarith [norm_quarterPoint_sub_one_le y])
      _ = 7*Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 7 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  norm_num at h
  change ‖FleetGammaKernel.psi (quarterPoint y)‖ ≤
    |Real.eulerMascheroniConstant|+5*(1+Real.log (2+‖quarterPoint y-1‖))+4 at h
  linarith

def shiftedWeight (N : ℕ) (q u : ℝ) : ℝ :=
  efficientPsiApprox N (q/2+u)-Real.log Real.pi

lemma shiftedWeight_eq (N : ℕ) (q u : ℝ) :
    shiftedWeight N q u = efficientWeightApprox N (q+2*u) := by
  unfold shiftedWeight efficientWeightApprox
  congr 2
  ring

theorem abs_shiftedWeight_le (N : ℕ) (hN : 2 ≤ N) {q u : ℝ}
    (hq : |q| ≤ 100) (hu : |u| ≤ 12) : |shiftedWeight N q u| ≤ 49 := by
  have hy : |q/2+u| ≤ 62 := by
    have h := abs_add_le (q/2) u
    norm_num [abs_div] at h
    linarith
  have he := abs_re_psi_sub_efficientPsiApprox_le N hN (q/2+u)
  have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
  have he1 : 1/((N:ℝ)-1)^2 ≤ 1 := by
    rw [div_le_iff₀ (sq_pos_of_pos (show 0 < (N:ℝ)-1 by linarith))]
    nlinarith
  have hb := abs_add_le
    (efficientPsiApprox N (q/2+u)-(FleetGammaKernel.psi (quarterPoint (q/2+u))).re)
    ((FleetGammaKernel.psi (quarterPoint (q/2+u))).re-Real.log Real.pi)
  have hc := abs_sub (FleetGammaKernel.psi (quarterPoint (q/2+u))).re (Real.log Real.pi)
  have hd := (Complex.abs_re_le_norm _).trans (norm_psi_le_forty_five hy)
  rw [abs_sub_comm] at he
  unfold shiftedWeight
  have heq : efficientPsiApprox N (q/2+u)-Real.log Real.pi =
      (efficientPsiApprox N (q/2+u)-(FleetGammaKernel.psi (quarterPoint (q/2+u))).re)+
      ((FleetGammaKernel.psi (quarterPoint (q/2+u))).re-Real.log Real.pi) := by ring
  rw [heq]
  linarith [abs_log_pi_le_three]

lemma hasDerivAt_shiftedWeight (N : ℕ) (q u : ℝ) :
    HasDerivAt (shiftedWeight N q) (first N (q/2+u)) u := by
  have h := ((hasDerivAt_efficientPsiApprox N (q/2+u)).comp u
    ((hasDerivAt_id u).const_add (q/2))).sub_const (Real.log Real.pi)
  simp only [mul_one] at h
  exact h

lemma hasDerivAt_shiftedFirst (N : ℕ) (q u : ℝ) :
    HasDerivAt (fun v => first N (q/2+v)) (second N (q/2+u)) u := by
  have h := (hasDerivAt_first N (q/2+u)).comp u
    ((hasDerivAt_id u).const_add (q/2))
  simp only [mul_one] at h
  exact h

lemma hasDerivAt_gaussian (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (-v^2)) (-2*u*Real.exp (-u^2)) u := by
  convert ((hasDerivAt_id u).pow 2).neg.exp using 1
  · rfl
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
  push_cast
  ring

def integrandFirst (N : ℕ) (q u : ℝ) : ℝ :=
  Real.exp (-u^2)*(-2*u*shiftedWeight N q u+first N (q/2+u))

def integrandSecond (N : ℕ) (q u : ℝ) : ℝ :=
  Real.exp (-u^2)*((4*u^2-2)*shiftedWeight N q u-
    4*u*first N (q/2+u)+second N (q/2+u))

theorem hasDerivAt_integrand (N : ℕ) (q u : ℝ) :
    HasDerivAt (FleetEfficientArchimedeanCertificate.efficientIntegrand N q)
      (integrandFirst N q u) u := by
  have hh := (hasDerivAt_gaussian u).mul (hasDerivAt_shiftedWeight N q u)
  convert hh using 1
  · ext v
    simp only [FleetEfficientArchimedeanCertificate.efficientIntegrand, Pi.mul_apply,
      shiftedWeight_eq]
  · unfold integrandFirst
    ring

theorem hasDerivAt_integrandFirst (N : ℕ) (q u : ℝ) :
    HasDerivAt (integrandFirst N q) (integrandSecond N q u) u := by
  have hh := (hasDerivAt_gaussian u).mul
    ((((hasDerivAt_id u).const_mul (-2)).mul (hasDerivAt_shiftedWeight N q u)).add
      (hasDerivAt_shiftedFirst N q u))
  convert hh using 1
  · rfl
  unfold integrandSecond
  simp only [id_eq, Pi.mul_apply, Pi.add_apply]
  ring

lemma gaussian_le_one (u : ℝ) : Real.exp (-u^2) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg u]

lemma gaussian_mul_sq_le_one (u : ℝ) : Real.exp (-u^2)*u^2 ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u^2))
    (Real.exp_pos (-u^2)).le
  have he : Real.exp (-u^2)*Real.exp (u^2) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [he] at h
  nlinarith [Real.exp_pos (-u^2)]

lemma gaussian_mul_abs_le_two (u : ℝ) : Real.exp (-u^2)*|u| ≤ 2 := by
  have hu : |u| ≤ 1+u^2 := by
    nlinarith [sq_nonneg (|u|-1), _root_.sq_abs u]
  have h := mul_le_mul_of_nonneg_left hu (Real.exp_pos (-u^2)).le
  nlinarith [gaussian_le_one u, gaussian_mul_sq_le_one u]

/-- A concrete uniform curvature bound on the full stage-100 quadrature domain.
The finite formula uses the same imaginary coordinate `q/2+u`, so no extra
chain-rule factor is lost when passing from the digamma derivatives. -/
theorem abs_integrandSecond_le (N : ℕ) (hN : 2 ≤ N) {q u : ℝ}
    (hq : |q| ≤ 100) (hu : |u| ≤ 12) : |integrandSecond N q u| ≤ 1000 := by
  have hw := abs_shiftedWeight_le N hN hq hu
  have h1 := abs_first_le N hN (q/2+u)
  have h2 := abs_second_le N hN (q/2+u)
  have hc : |4*u^2-2| ≤ 4*u^2+2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg u]
  have hb : |(4*u^2-2)*shiftedWeight N q u-
      4*u*first N (q/2+u)+second N (q/2+u)| ≤
      (4*u^2+2)*49+4*|u| *22+162 := by
    calc
      _ ≤ |(4*u^2-2)*shiftedWeight N q u|+
          |4*u*first N (q/2+u)|+|second N (q/2+u)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
      _ = |4*u^2-2| * |shiftedWeight N q u|+
          4*|u| * |first N (q/2+u)|+|second N (q/2+u)| := by
        simp only [abs_mul]
        norm_num
      _ ≤ _ := add_le_add
        (add_le_add (mul_le_mul hc hw (abs_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left h1 (by positivity))) h2
  unfold integrandSecond
  rw [abs_mul, _root_.abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-u^2)*((4*u^2+2)*49+4*|u| *22+162) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = 49*(4*(Real.exp (-u^2)*u^2)+2*Real.exp (-u^2))+
        88*(Real.exp (-u^2)*|u|)+162*Real.exp (-u^2) := by ring
    _ ≤ 1000 := by
      nlinarith [gaussian_le_one u, gaussian_mul_sq_le_one u, gaussian_mul_abs_le_two u]

theorem continuous_integrand (N : ℕ) (q : ℝ) :
    Continuous (FleetEfficientArchimedeanCertificate.efficientIntegrand N q) :=
  continuous_iff_continuousAt.mpr (fun u => (hasDerivAt_integrand N q u).continuousAt)

end FleetEfficientArchimedeanDerivatives
