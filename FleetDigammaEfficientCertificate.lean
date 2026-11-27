import FleetDigammaIntervalCertificate
import Mathlib

noncomputable section
open Complex Finset Filter
open scoped Topology

namespace FleetDigammaEfficientCertificate

def asymptotic (z : ℂ) : ℝ := (Complex.log z).re - (z⁻¹).re / 2

private lemma logTaylor_three (v : ℂ) : Complex.logTaylor 3 v = v - v^2/2 := by
  norm_num [Complex.logTaylor, Finset.sum_range_succ]
  ring

private lemma cubic_log_step_bound (v : ℂ) (hv : ‖v‖ ≤ 1/2) :
    ‖Complex.log (1+v) - v + v^2/(2*(1+v))‖ ≤ 2*‖v‖^3 := by
  have hv1 : ‖v‖ < 1 := lt_of_le_of_lt hv (by norm_num)
  have hi : (1-‖v‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    rw [show (2:ℝ)⁻¹ = 1/2 by norm_num]
    linarith
  have ht := Complex.norm_log_sub_logTaylor_le 2 hv1
  rw [logTaylor_three] at ht
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at ht
  have hn : 1+v ≠ 0 := Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one hv1)
  have hiC : ‖(1+v)⁻¹‖ ≤ 2 := by
    have h := Complex.norm_one_add_mul_inv_le (t := 1) (by simp) hv1
    simpa using h.trans hi
  have he : Complex.log (1+v) - v + v^2/(2*(1+v)) =
      (Complex.log (1+v) - (v-v^2/2)) - v^3/2*(1+v)⁻¹ := by
    field_simp [hn]
    ring
  rw [he]
  have hcorr : ‖v^3/2*(1+v)⁻¹‖ ≤ ‖v‖^3 := by
    rw [norm_mul, norm_div, norm_pow]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
    nlinarith [mul_le_mul_of_nonneg_left hiC (pow_nonneg (norm_nonneg v) 3)]
  refine (norm_sub_le _ _).trans ?_
  have hp := mul_le_mul_of_nonneg_left hi (pow_nonneg (norm_nonneg v) 3)
  nlinarith [pow_nonneg (norm_nonneg v) 3]

lemma asymptotic_step_bound (w : ℂ) (hw : 2 ≤ w.re) :
    |asymptotic (w+1) - asymptotic w - (w⁻¹).re| ≤ 2/(w.re)^3 := by
  have hr : 0 < w.re := by linarith
  have hn : w ≠ 0 := by intro h; simp [h] at hr
  have hn1 : w+1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hnorm : w.re ≤ ‖w‖ := Complex.re_le_norm w
  have hv : ‖w⁻¹‖ ≤ 1/2 := by
    rw [norm_inv]
    refine (inv_anti₀ hr hnorm).trans ?_
    simpa only [one_div] using one_div_le_one_div_of_le (show (0:ℝ)<2 by norm_num) hw
  have ht := cubic_log_step_bound (w⁻¹) hv
  have hlog : (Complex.log (w+1)).re - (Complex.log w).re =
      (Complex.log (1+w⁻¹)).re := by
    have he : 1+w⁻¹ = (w+1)/w := by field_simp
    simp only [Complex.log_re, he]
    change Real.log ‖w+1‖ - Real.log ‖w‖ = Real.log ‖(w+1)/w‖
    rw [norm_div]
    rw [Real.log_div (norm_ne_zero_iff.mpr hn1) (norm_ne_zero_iff.mpr hn)]
  have he : asymptotic (w+1) - asymptotic w - (w⁻¹).re =
      (Complex.log (1+w⁻¹) - w⁻¹ + (w⁻¹)^2/(2*(1+w⁻¹))).re := by
    have hnv : 1+w⁻¹ ≠ 0 := by
      have he : 1+w⁻¹ = (w+1)/w := by field_simp
      rw [he]
      exact div_ne_zero hn1 hn
    have hc : w⁻¹ - (w+1)⁻¹ = (w⁻¹)^2/(1+w⁻¹) := by
      field_simp [hn, hn1, hnv]
      ring
    have hc' : ((w⁻¹)^2/(2*(1+w⁻¹))).re =
        ((w⁻¹).re - ((w+1)⁻¹).re)/2 := by
      rw [show (w⁻¹)^2/(2*(1+w⁻¹)) = (w⁻¹-(w+1)⁻¹)/2 by
        rw [hc]
        field_simp [hn, hn1, hnv]]
      simp [Complex.div_re, Complex.normSq]
    unfold asymptotic
    simp only [Complex.add_re, Complex.sub_re]
    rw [hc']
    linarith
  rw [he]
  refine ((Complex.abs_re_le_norm _).trans ht).trans ?_
  rw [norm_inv, inv_pow]
  change 2/‖w‖^3 ≤ 2/(w.re)^3
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  gcongr

open FleetDigammaIntervalCertificate

def center (N : ℕ) (y : ℝ) : ℝ :=
  asymptotic (quarterPoint y + N) -
    ∑ k ∈ range N, ((quarterPoint y + (k:ℂ))⁻¹).re

lemma two_inv_cube_le_sub_inv_sq {x : ℝ} (hx : 0 < x) :
    2/(x+1)^3 ≤ 1/x^2 - 1/(x+1)^2 := by
  apply sub_nonneg.mp
  have he : (1/x^2 - 1/(x+1)^2) - 2/(x+1)^3 =
      (3*x+1)/(x^2*(x+1)^3) := by
    field_simp
    ring
  rw [he]
  positivity

lemma center_increment_bound (N : ℕ) (hN : 2 ≤ N) (y : ℝ) :
    |center (N+1) y - center N y| ≤ 1/((N:ℝ)-1)^2 - 1/(N:ℝ)^2 := by
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hs := asymptotic_step_bound (quarterPoint y + N) (by
    simp only [Complex.add_re, quarterPoint_re, Complex.natCast_re]
    linarith)
  have he : center (N+1) y - center N y =
      asymptotic ((quarterPoint y + N)+1) - asymptotic (quarterPoint y+N) -
        ((quarterPoint y+N)⁻¹).re := by
    simp only [center, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    rw [← add_assoc (quarterPoint y) (N:ℂ) 1]
    ring
  rw [he]
  refine hs.trans ?_
  simp only [Complex.add_re, quarterPoint_re, Complex.natCast_re]
  calc
    2/(1/4+(N:ℝ))^3 ≤ 2/(N:ℝ)^3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      gcongr
      linarith
    _ ≤ 1/((N:ℝ)-1)^2 - 1/(N:ℝ)^2 := by
      simpa only [sub_add_cancel] using
        two_inv_cube_le_sub_inv_sq (x := (N:ℝ)-1) (by linarith)

theorem center_difference_bound (N m : ℕ) (hN : 2 ≤ N) (y : ℝ) :
    |center (N+m) y - center N y| ≤
      1/((N:ℝ)-1)^2 - 1/((N:ℝ)+m-1)^2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs := center_increment_bound (N+m) (by omega) y
    have he : center (N+(m+1)) y - center N y =
        (center (N+m+1) y - center (N+m) y) + (center (N+m) y - center N y) := by
      rw [Nat.add_assoc]
      ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    have hb := add_le_add hs ih
    simp only [Nat.cast_add, Nat.cast_one] at hb ⊢
    convert hb using 1
    ring

def logSumCenter (N : ℕ) (y : ℝ) : ℝ :=
  Real.log N - ∑ k ∈ range N, ((quarterPoint y + (k:ℂ))⁻¹).re

lemma arithmeticPsiApprox_diagonal (N : ℕ) (y : ℝ) :
    arithmeticPsiApprox N N y = logSumCenter N y := by
  have hH : (harmonic N : ℝ) = ∑ k ∈ range N, ((k:ℝ)+1)⁻¹ := by
    simp [harmonic]
  have hInv (k : ℕ) : (((k:ℂ)+1)⁻¹).re = ((k:ℝ)+1)⁻¹ := by
    have he : (k:ℂ)+1 = (((k:ℝ)+1 : ℝ):ℂ) := by push_cast; rfl
    rw [he, ← Complex.ofReal_inv, Complex.ofReal_re]
  have ha : arithmeticPsiApprox N N y = realPsiApprox N y +
      Real.eulerMascheroniConstant + Real.log N - (harmonic N:ℝ) := by
    unfold arithmeticPsiApprox realPsiApprox
    ring
  rw [ha, ← psiApprox_re]
  simp only [psiApprox, Complex.sub_re, Complex.neg_re, Complex.ofReal_re,
    Complex.re_sum, hInv, Finset.sum_sub_distrib, hH, logSumCenter]
  ring

lemma tendsto_logSumCenter (y : ℝ) :
    Tendsto (fun N : ℕ => logSumCenter N y) atTop
      (𝓝 (FleetGammaKernel.psi (quarterPoint y)).re) := by
  have hh : Tendsto (fun N : ℕ => arithmeticPsiApprox N N y) atTop
      (𝓝 (FleetGammaKernel.psi (quarterPoint y)).re) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) _
      (tendsto_const_div_atTop_nhds_zero_nat (4+4*|y|))
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [abs_sub_comm]
    refine (abs_re_psi_sub_arithmeticPsiApprox_le N N (by omega) (by omega) y).trans ?_
    apply le_of_eq
    ring
  simpa only [arithmeticPsiApprox_diagonal] using hh

lemma tendsto_asymptotic_sub_log_nat (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun N : ℕ => asymptotic (z+N) - Real.log N) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (N:ℂ)⁻¹) atTop (𝓝 0) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zero] using h
  have hv : Tendsto (fun N : ℕ => z/(N:ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hi
  have hbase : Tendsto (fun N : ℕ => 1+z/(N:ℂ)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hv
  have hlog : Tendsto (fun N : ℕ => Real.log ‖1+z/(N:ℂ)‖) atTop (𝓝 0) := by
    have h := hbase.norm.log (by norm_num : ‖(1:ℂ)‖ ≠ 0)
    simpa using h
  have hInv : Tendsto (fun N : ℕ => (1+z/(N:ℂ))⁻¹*(N:ℂ)⁻¹) atTop (𝓝 0) := by
    simpa using (hbase.inv₀ (by norm_num)).mul hi
  have hRe := Complex.continuous_re.continuousAt.tendsto.comp hInv
  have ht := hlog.sub (hRe.div_const 2)
  simp only [Complex.zero_re, zero_div, sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hn : (N:ℂ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
  have hw : z+(N:ℂ) ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp at h
    linarith
  have he : 1+z/(N:ℂ) = (z+N)/(N:ℂ) := by field_simp; ring
  have hinv : (1+z/(N:ℂ))⁻¹*(N:ℂ)⁻¹ = (z+N)⁻¹ := by
    rw [he, inv_div]
    field_simp
  simp only [Function.comp_def, asymptotic, hinv, Complex.log_re]
  change Real.log ‖1+z/(N:ℂ)‖ - ((z+N)⁻¹).re/2 =
    Real.log ‖z+N‖ - ((z+N)⁻¹).re/2 - Real.log N
  rw [he, norm_div, Complex.norm_natCast,
    Real.log_div (norm_ne_zero_iff.mpr hw) (ne_of_gt hNr)]
  ring

theorem tendsto_center (y : ℝ) :
    Tendsto (fun N : ℕ => center N y) atTop
      (𝓝 (FleetGammaKernel.psi (quarterPoint y)).re) := by
  have h := (tendsto_asymptotic_sub_log_nat (quarterPoint y) (by
    rw [quarterPoint_re]
    norm_num)).add (tendsto_logSumCenter y)
  simp only [zero_add] at h
  convert h using 1
  funext N
  unfold center logSumCenter
  ring

/-- Uniform accelerated digamma error, with no bound on the imaginary part. -/
theorem abs_re_psi_sub_center_le (N : ℕ) (hN : 2 ≤ N) (y : ℝ) :
    |(FleetGammaKernel.psi (quarterPoint y)).re - center N y| ≤
      1/((N:ℝ)-1)^2 := by
  have ht : Tendsto (fun m : ℕ => center (N+m) y) atTop
      (𝓝 (FleetGammaKernel.psi (quarterPoint y)).re) := by
    have h := (tendsto_center y).comp (tendsto_add_atTop_nat N)
    simpa only [Function.comp_def, Nat.add_comm] using h
  apply le_of_tendsto (ht.sub_const (center N y)).abs
  exact Filter.Eventually.of_forall (fun m =>
    (center_difference_bound N m hN y).trans (sub_le_self _ (by positivity)))

def efficientPsiApprox (N : ℕ) (y : ℝ) : ℝ :=
  Real.log (((N:ℝ)+1/4)^2+y^2)/2 -
    ((N:ℝ)+1/4)/(2*(((N:ℝ)+1/4)^2+y^2)) -
      ∑ k ∈ range N, ((k:ℝ)+1/4)/(((k:ℝ)+1/4)^2+y^2)

lemma quarter_inv_re (N : ℕ) (y : ℝ) :
    ((quarterPoint y + (N:ℂ))⁻¹).re =
      ((N:ℝ)+1/4)/(((N:ℝ)+1/4)^2+y^2) := by
  simp [quarterPoint, Complex.inv_re, Complex.normSq, pow_two,
    add_comm, add_left_comm, add_assoc]

lemma center_eq_efficientPsiApprox (N : ℕ) (y : ℝ) :
    center N y = efficientPsiApprox N y := by
  have hl (w : ℂ) : (Complex.log w).re = Real.log (Complex.normSq w)/2 := by
    rw [Complex.log_re, Complex.normSq_eq_norm_sq, Real.log_pow]
    norm_num
  unfold center efficientPsiApprox asymptotic
  rw [hl, quarter_inv_re]
  simp_rw [quarter_inv_re]
  have hsq : Complex.normSq (quarterPoint y + (N:ℂ)) = ((N:ℝ)+1/4)^2+y^2 := by
    simp [quarterPoint, Complex.normSq, pow_two, add_comm, add_left_comm, add_assoc]
  rw [hsq]
  rw [div_div, mul_comm (((N:ℝ)+1/4)^2+y^2) 2]

/-- The finite real approximation consists of `N` rational terms and one real
logarithm. Its error is quadratic in the cutoff and uniform in `y`. -/
theorem abs_re_psi_sub_efficientPsiApprox_le (N : ℕ) (hN : 2 ≤ N) (y : ℝ) :
    |(FleetGammaKernel.psi (quarterPoint y)).re - efficientPsiApprox N y| ≤
      1/((N:ℝ)-1)^2 := by
  rw [← center_eq_efficientPsiApprox]
  exact abs_re_psi_sub_center_le N hN y

def efficientWeightApprox (N : ℕ) (t : ℝ) : ℝ :=
  efficientPsiApprox N (t/2) - Real.log Real.pi

theorem abs_weight_sub_efficientWeightApprox_le (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    |FleetGammaKernel.weight t - efficientWeightApprox N t| ≤ 1/((N:ℝ)-1)^2 := by
  have he : (1/4:ℂ)+(t:ℂ)*I/2 = quarterPoint (t/2) := by
    unfold quarterPoint
    push_cast
    ring
  unfold FleetGammaKernel.weight efficientWeightApprox
  rw [he, sub_sub_sub_cancel_right]
  exact abs_re_psi_sub_efficientPsiApprox_le N hN (t/2)

end FleetDigammaEfficientCertificate
