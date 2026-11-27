import FleetEfficientMidpointCertificate

/-! Sharper bounds for the existing 32-term Gaussian integrand allow a
4096-cell midpoint certificate without changing the earlier certificates. -/

noncomputable section
open Real Set MeasureTheory Finset
open FleetDigammaEfficientCertificate FleetDigammaIntervalCertificate
open FleetEfficientArchimedeanCertificate FleetEfficientArchimedeanDerivatives
open FleetEfficientMidpointCertificate

namespace FleetSharpMidpointCertificate

lemma gaussian_mul_abs_le_half (u : ℝ) : Real.exp (-u^2)*|u| ≤ 1/2 := by
  have hl : 2*|u| ≤ Real.exp (u^2) := by
    nlinarith [Real.add_one_le_exp (u^2), sq_nonneg (|u|-1), sq_abs u]
  have h := mul_le_mul_of_nonneg_left hl (Real.exp_pos (-u^2)).le
  have he : Real.exp (-u^2)*Real.exp (u^2) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [he] at h
  linarith

lemma gaussian_mul_curvature_le_two (u : ℝ) :
    Real.exp (-u^2)*|4*u^2-2| ≤ 2 := by
  have hl := Real.add_one_le_exp (u^2/2)
  have hs := mul_self_le_mul_self (show 0 ≤ u^2/2+1 by positivity) hl
  have hehalf : Real.exp (u^2/2)*Real.exp (u^2/2) = Real.exp (u^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hehalf] at hs
  have hmajor : |4*u^2-2| ≤ 2*Real.exp (u^2) := by
    apply abs_le.mpr
    constructor
    · nlinarith [Real.add_one_le_exp (u^2), sq_nonneg u]
    · nlinarith [sq_nonneg (u^2/2-1)]
  have h := mul_le_mul_of_nonneg_left hmajor (Real.exp_pos (-u^2)).le
  have he : Real.exp (-u^2)*Real.exp (u^2) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith

lemma sum_recip_thirty_two_le_eight :
    (∑ k ∈ range 32, 1/((k:ℝ)+1/4)) ≤ 8 := by
  norm_num [Finset.sum_range_succ]

lemma psi_rational_sum_le_eight (y : ℝ) :
    (∑ k ∈ range 32, ((k:ℝ)+1/4)/(((k:ℝ)+1/4)^2+y^2)) ≤ 8 := by
  refine (sum_le_sum (fun k _ => ?_)).trans sum_recip_thirty_two_le_eight
  have hk : 0 < (k:ℝ)+1/4 := by positivity
  rw [div_le_div_iff₀ (by positivity : 0 < ((k:ℝ)+1/4)^2+y^2) hk]
  nlinarith [sq_nonneg y]

lemma abs_efficientWeight_thirty_two_le {y : ℝ} (hy : |y| ≤ 62) :
    |efficientPsiApprox 32 y-Real.log Real.pi| ≤ 12 := by
  let D : ℝ := ((32:ℝ)+1/4)^2+y^2
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [sq_nonneg y]
  have hDy : y^2 ≤ 62^2 := by
    nlinarith [sq_abs y, mul_self_le_mul_self (abs_nonneg y) hy]
  have hDu : D ≤ (2:ℝ)^14 := by dsimp [D]; norm_num; nlinarith
  have hlog0 : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlog : Real.log D ≤ 14 := by
    calc
      _ ≤ Real.log ((2:ℝ)^14) := Real.log_le_log (by linarith) hDu
      _ = 14*Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 14 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have hc0 : 0 ≤ ((32:ℝ)+1/4)/(2*D) := by positivity
  have hc : ((32:ℝ)+1/4)/(2*D) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < 2*D)]
    dsimp [D]
    nlinarith [sq_nonneg y]
  have hs0 : 0 ≤ (∑ k ∈ range 32, ((k:ℝ)+1/4)/(((k:ℝ)+1/4)^2+y^2)) :=
    sum_nonneg (fun _ _ => by positivity)
  have hs := psi_rational_sum_le_eight y
  have hp := abs_le.mp abs_log_pi_le_three
  unfold efficientPsiApprox
  change |Real.log D/2-((32:ℝ)+1/4)/(2*D)-
    (∑ k ∈ range 32, ((k:ℝ)+1/4)/(((k:ℝ)+1/4)^2+y^2))-Real.log Real.pi| ≤ 12
  apply abs_le.mpr
  constructor <;> linarith

lemma abs_shiftedWeight_thirty_two_le {q u : ℝ} (hq : |q| ≤ 100) (hu : |u| ≤ 12) :
    |shiftedWeight 32 q u| ≤ 12 := by
  apply abs_efficientWeight_thirty_two_le
  have h := abs_add_le (q/2) u
  norm_num [abs_div] at h
  linarith

theorem abs_integrandSecond_thirty_two_le_230 {q u : ℝ}
    (hq : |q| ≤ 100) (hu : |u| ≤ 12) : |integrandSecond 32 q u| ≤ 230 := by
  have hw := abs_shiftedWeight_thirty_two_le hq hu
  have h1 := abs_first_le 32 (by norm_num) (q/2+u)
  have h2 := abs_second_le 32 (by norm_num) (q/2+u)
  have hb : |(4*u^2-2)*shiftedWeight 32 q u-
      4*u*first 32 (q/2+u)+second 32 (q/2+u)| ≤
      |4*u^2-2| *12+4*|u| *22+162 := by
    calc
      _ ≤ |(4*u^2-2)*shiftedWeight 32 q u|+
          |4*u*first 32 (q/2+u)|+|second 32 (q/2+u)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
      _ = |4*u^2-2| * |shiftedWeight 32 q u|+
          4*|u| * |first 32 (q/2+u)|+|second 32 (q/2+u)| := by
        simp only [abs_mul]
        norm_num
      _ ≤ _ := add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hw (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h1 (by positivity))) h2
  unfold integrandSecond
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-u^2)*(|4*u^2-2| *12+4*|u| *22+162) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = 12*(Real.exp (-u^2)*|4*u^2-2|)+
        88*(Real.exp (-u^2)*|u|)+162*Real.exp (-u^2) := by ring
    _ ≤ 230 := by
      linarith [gaussian_le_one u, gaussian_mul_curvature_le_two u, gaussian_mul_abs_le_half u]

theorem abs_integrandSecond_thirty_two_le_256 {q u : ℝ}
    (hq : |q| ≤ 100) (hu : |u| ≤ 12) : |integrandSecond 32 q u| ≤ 256 :=
  (abs_integrandSecond_thirty_two_le_230 hq hu).trans (by norm_num)

theorem midpoint_error_sharp {q : ℝ} (hq : |q| ≤ 100) (n : ℕ) (hn : 0 < n) :
    |(∫ u : ℝ in Ioc (-12) 12, efficientIntegrand 32 q u)-midpointSum 32 q n| ≤
      147456/(n:ℝ)^2 := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hend : (-12:ℝ)+(n:ℝ)*(24/(n:ℝ)) = 12 := by field_simp; ring
  have hb : ∀ t ∈ Icc (-12:ℝ) (-12+(n:ℝ)*(24/(n:ℝ))),
      |integrandSecond 32 q t| ≤ 256 := by
    intro t ht
    rw [hend] at ht
    exact abs_integrandSecond_thirty_two_le_256 hq (abs_le.mpr ht)
  have h := FleetMidpointDerivativeGrid.uniform_midpoint_error_of_hasDerivAt
    (hasDerivAt_integrand 32 q) (hasDerivAt_integrandFirst 32 q)
    (-12) (24/(n:ℝ)) 256 n (by positivity) hb
  rw [hend, intervalIntegral.integral_of_le (show (-12:ℝ) ≤ 12 by norm_num)] at h
  change |(∫ u : ℝ in Ioc (-12) 12, efficientIntegrand 32 q u)-midpointSum 32 q n| ≤ _ at h
  convert h using 1
  field_simp
  ring

theorem normalized_midpoint_error_sharp {q : ℝ} (hq : |q| ≤ 100)
    (n : ℕ) (hn : 0 < n) :
    |(1/sqrt Real.pi)*(∫ u : ℝ in Ioc (-12) 12, efficientIntegrand 32 q u)-
      (1/sqrt Real.pi)*midpointSum 32 q n| ≤
      147456/((n:ℝ)^2*sqrt Real.pi) := by
  rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ 1/sqrt Real.pi by positivity)]
  have h := mul_le_mul_of_nonneg_left (midpoint_error_sharp hq n hn)
    (show 0 ≤ 1/sqrt Real.pi by positivity)
  convert h using 1
  ring

theorem actual_normalized_midpoint_error_sharp {q : ℝ} (hq : |q| ≤ 100)
    (n : ℕ) (hn : 0 < n) :
    |(1/sqrt Real.pi)*
      (∫ u : ℝ in Ioc (-12) 12, FleetArchimedeanTailCertificate.integrand q u)-
      (1/sqrt Real.pi)*midpointSum 32 q n| ≤
      1/961+147456/((n:ℝ)^2*sqrt Real.pi) := by
  have h1 := normalized_replacement_thirty_two q
  have h2 := normalized_midpoint_error_sharp hq n hn
  exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)

/-- A four-times smaller concrete grid, with a fully proved total analytic
error of at most 0.00625 for the original truncated Gaussian integral. -/
theorem actual_normalized_midpoint_4096_le {q : ℝ} (hq : |q| ≤ 100) :
    |(1/sqrt Real.pi)*
      (∫ u : ℝ in Ioc (-12) 12, FleetArchimedeanTailCertificate.integrand q u)-
      (1/sqrt Real.pi)*midpointSum 32 q 4096| ≤ (1/160:ℝ) := by
  have h := actual_normalized_midpoint_error_sharp hq 4096 (by norm_num)
  have hs : (12/7:ℝ) ≤ sqrt Real.pi := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi, Real.pi_gt_three]
  have hb : (147456:ℝ)/((4096:ℝ)^2*sqrt Real.pi) ≤ (7/12)*(147456/(4096:ℝ)^2) := by
    rw [div_le_iff₀ (by positivity : 0 < (4096:ℝ)^2*sqrt Real.pi)]
    nlinarith
  have he : (1/961:ℝ)+(7/12)*(147456/(4096:ℝ)^2) ≤ 1/160 := by norm_num
  have hh := (add_le_add_right hb (1/961)).trans he
  norm_num at hh h
  simpa only [one_div] using h.trans hh

end FleetSharpMidpointCertificate
