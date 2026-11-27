import FleetGammaIdentification
import FleetDigammaGrowth
import FleetGammaKernel
import Mathlib

/-!
# Proved finite digamma enclosures

The finite sums below approximate the actual logarithmic derivative of Gamma.
Their errors are proved from the identified partial-fraction series. No
externally computed numerical enclosure is an assumption of these theorems.
-/

noncomputable section
open Complex Finset

namespace FleetDigammaIntervalCertificate

def psiApprox (N : ℕ) (z : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) -
    ∑ k ∈ range N, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹)

theorem norm_psi_sub_psiApprox_le (N : ℕ) (hN : 0 < N)
    {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hz : δ ≤ z.re) :
    ‖FleetGammaKernel.psi z - psiApprox N z‖ ≤
      (‖z - 1‖ / δ) / (N : ℝ) := by
  have hs := FleetDigammaSeries.summable_deriv_q (lt_of_lt_of_le hδ hz)
  rw [FleetGammaKernel.psi, FleetGammaIdentification.digamma_eq_series z
    (lt_of_lt_of_le hδ hz)]
  rw [← Summable.sum_add_tsum_nat_add N hs]
  have he : -(Real.eulerMascheroniConstant : ℂ) -
      ((∑ k ∈ range N, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹)) +
        ∑' k : ℕ, ((z + ((k + N : ℕ) : ℂ))⁻¹ - (((k + N : ℕ) : ℂ) + 1)⁻¹)) -
      psiApprox N z =
      -(∑' k : ℕ, ((z + ((k + N : ℕ) : ℂ))⁻¹ - (((k + N : ℕ) : ℂ) + 1)⁻¹)) := by
    unfold psiApprox
    ring
  rw [he, norm_neg]
  exact FleetDigammaGrowth.norm_tail_le N hN hδ hδ1 hz

def quarterPoint (y : ℝ) : ℂ := 1 / 4 + (y : ℂ) * I

lemma quarterPoint_re (y : ℝ) : (quarterPoint y).re = 1 / 4 := by
  simp [quarterPoint]

lemma norm_quarterPoint_sub_one_le (y : ℝ) :
    ‖quarterPoint y - 1‖ ≤ 3 / 4 + |y| := by
  have h := Complex.norm_le_abs_re_add_abs_im (quarterPoint y - 1)
  norm_num [quarterPoint] at h ⊢
  exact h

theorem norm_quarter_psi_sub_psiApprox_le (N : ℕ) (hN : 0 < N) (y : ℝ) :
    ‖FleetGammaKernel.psi (quarterPoint y) - psiApprox N (quarterPoint y)‖ ≤
      (3 + 4 * |y|) / (N : ℝ) := by
  refine (norm_psi_sub_psiApprox_le N hN (δ := 1/4) (by norm_num)
    (by norm_num) (by rw [quarterPoint_re])).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := norm_quarterPoint_sub_one_le y
  linarith

def realPsiApprox (N : ℕ) (y : ℝ) : ℝ :=
  -Real.eulerMascheroniConstant +
    ∑ k ∈ range N, (1 / ((k : ℝ) + 1) -
      ((k : ℝ) + 1/4) / (((k : ℝ) + 1/4)^2 + y^2))

lemma psiApprox_re (N : ℕ) (y : ℝ) :
    (psiApprox N (quarterPoint y)).re = realPsiApprox N y := by
  simp only [psiApprox, realPsiApprox, Complex.sub_re, Complex.neg_re,
    Complex.ofReal_re, Complex.re_sum]
  rw [sub_eq_add_neg]
  rw [← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp [quarterPoint, Complex.inv_re, Complex.normSq, pow_two]
  ring

theorem abs_re_psi_sub_realPsiApprox_le (N : ℕ) (hN : 0 < N) (y : ℝ) :
    |(FleetGammaKernel.psi (quarterPoint y)).re - realPsiApprox N y| ≤
      (3 + 4 * |y|) / (N : ℝ) := by
  rw [← psiApprox_re]
  exact (Complex.abs_re_le_norm (_ - _)).trans
    (norm_quarter_psi_sub_psiApprox_le N hN y)

theorem re_psi_mem_finite_interval (N : ℕ) (hN : 0 < N) (y : ℝ) :
    realPsiApprox N y - (3 + 4 * |y|) / (N : ℝ) ≤
        (FleetGammaKernel.psi (quarterPoint y)).re ∧
      (FleetGammaKernel.psi (quarterPoint y)).re ≤
        realPsiApprox N y + (3 + 4 * |y|) / (N : ℝ) := by
  have h := abs_le.mp (abs_re_psi_sub_realPsiApprox_le N hN y)
  constructor <;> linarith

def eulerApprox (K : ℕ) : ℝ := (harmonic K : ℝ) - Real.log K

theorem abs_euler_sub_eulerApprox_le (K : ℕ) (hK : 0 < K) :
    |Real.eulerMascheroniConstant - eulerApprox K| ≤ 1 / (K : ℝ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hu := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' K
  have hl := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant K
  simp only [Real.eulerMascheroniSeq', Nat.ne_of_gt hK, if_false] at hu
  change (harmonic K : ℝ) - Real.log ((K : ℝ) + 1) < _ at hl
  have hlog : Real.log ((K : ℝ) + 1) - Real.log K ≤ 1 / (K : ℝ) := by
    rw [← Real.log_div (by positivity) (ne_of_gt hKr)]
    calc
      _ ≤ ((K : ℝ) + 1) / K - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / (K : ℝ) := by field_simp; ring
  unfold eulerApprox
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- This approximation contains only finite rational operations and one real
logarithm. In particular it does not contain Euler's constant or Gamma. -/
def arithmeticPsiApprox (N K : ℕ) (y : ℝ) : ℝ :=
  Real.log K - (harmonic K : ℝ) +
    ∑ k ∈ range N, (1 / ((k : ℝ) + 1) -
      ((k : ℝ) + 1/4) / (((k : ℝ) + 1/4)^2 + y^2))

theorem abs_re_psi_sub_arithmeticPsiApprox_le
    (N K : ℕ) (hN : 0 < N) (hK : 0 < K) (y : ℝ) :
    |(FleetGammaKernel.psi (quarterPoint y)).re - arithmeticPsiApprox N K y| ≤
      (3 + 4 * |y|) / (N : ℝ) + 1 / (K : ℝ) := by
  have he : (FleetGammaKernel.psi (quarterPoint y)).re - arithmeticPsiApprox N K y =
      ((FleetGammaKernel.psi (quarterPoint y)).re - realPsiApprox N y) -
        (Real.eulerMascheroniConstant - eulerApprox K) := by
    unfold arithmeticPsiApprox realPsiApprox eulerApprox
    ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add
    (abs_re_psi_sub_realPsiApprox_le N hN y) (abs_euler_sub_eulerApprox_le K hK))

theorem re_psi_mem_arithmetic_interval
    (N K : ℕ) (hN : 0 < N) (hK : 0 < K) (y : ℝ) :
    arithmeticPsiApprox N K y - ((3 + 4 * |y|) / (N : ℝ) + 1 / (K : ℝ)) ≤
        (FleetGammaKernel.psi (quarterPoint y)).re ∧
      (FleetGammaKernel.psi (quarterPoint y)).re ≤
        arithmeticPsiApprox N K y + ((3 + 4 * |y|) / (N : ℝ) + 1 / (K : ℝ)) := by
  have h := abs_le.mp (abs_re_psi_sub_arithmeticPsiApprox_le N K hN hK y)
  constructor <;> linarith

/-- A numerical baseline bound for the actual digamma value at one quarter. -/
theorem abs_re_psi_quarter_le_five :
    |(FleetGammaKernel.psi (quarterPoint 0)).re| ≤ 5 := by
  have h := abs_le.mp (abs_re_psi_sub_realPsiApprox_le 4 (by norm_num) 0)
  have hl := Real.one_half_lt_eulerMascheroniConstant
  have hu := Real.eulerMascheroniConstant_lt_two_thirds
  norm_num [realPsiApprox, Finset.sum_range_succ] at h
  apply abs_le.mpr
  constructor <;> linarith

/-- A simple global polynomial envelope; constants are deliberately coarse. -/
theorem norm_psi_quarter_le (y : ℝ) :
    ‖FleetGammaKernel.psi (quarterPoint y)‖ ≤ 19 + 5 * |y| := by
  have hz : 0 < (quarterPoint y).re := by rw [quarterPoint_re]; norm_num
  have h := FleetDigammaGrowth.norm_logDerivative_le
    (z := quarterPoint y) (δ := 1/4) (by norm_num) (by norm_num)
    (by rw [quarterPoint_re])
  rw [← FleetGammaIdentification.digamma_eq_series _ hz] at h
  change ‖FleetGammaKernel.psi (quarterPoint y)‖ ≤ _ at h
  have hγ : |Real.eulerMascheroniConstant| ≤ 1 := by
    rw [_root_.abs_of_nonneg (by linarith [Real.one_half_lt_eulerMascheroniConstant])]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < 2 + ‖quarterPoint y - 1‖ by positivity)
  have hn := norm_quarterPoint_sub_one_le y
  norm_num at h
  change ‖FleetGammaKernel.psi (quarterPoint y)‖ ≤
    |Real.eulerMascheroniConstant| + 5 * (1 + Real.log (2 + ‖quarterPoint y - 1‖)) + 4 at h
  linarith

theorem abs_log_pi_le_three : |Real.log Real.pi| ≤ 3 := by
  rw [_root_.abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
  have h := Real.log_le_sub_one_of_pos Real.pi_pos
  linarith [Real.pi_lt_four]

/-- Explicit unconditional bound on the exact archimedean kernel used in the
full-line arithmetic functional. -/
theorem abs_weight_le (t : ℝ) : |FleetGammaKernel.weight t| ≤ 22 + 10 * |t| := by
  have he : (1/4 : ℂ) + (t : ℂ) * I / 2 = quarterPoint (t/2) := by
    unfold quarterPoint
    push_cast
    ring
  unfold FleetGammaKernel.weight
  rw [he]
  have h := (abs_sub ((FleetGammaKernel.psi (quarterPoint (t/2))).re)
    (Real.log Real.pi)).trans
    (add_le_add ((Complex.abs_re_le_norm _).trans (norm_psi_quarter_le (t/2)))
      abs_log_pi_le_three)
  norm_num [abs_div] at h
  linarith [abs_nonneg t]

/-- The finite arithmetic approximation in the original kernel variable. -/
def arithmeticWeightApprox (N K : ℕ) (t : ℝ) : ℝ :=
  arithmeticPsiApprox N K (t/2) - Real.log Real.pi

theorem abs_weight_sub_arithmeticWeightApprox_le
    (N K : ℕ) (hN : 0 < N) (hK : 0 < K) (t : ℝ) :
    |FleetGammaKernel.weight t - arithmeticWeightApprox N K t| ≤
      (3 + 2 * |t|) / (N : ℝ) + 1 / (K : ℝ) := by
  have he : (1/4 : ℂ) + (t : ℂ) * I / 2 = quarterPoint (t/2) := by
    unfold quarterPoint
    push_cast
    ring
  unfold FleetGammaKernel.weight arithmeticWeightApprox
  rw [he, sub_sub_sub_cancel_right]
  have h := abs_re_psi_sub_arithmeticPsiApprox_le N K hN hK (t/2)
  convert h using 1
  simp [abs_div]
  ring

end FleetDigammaIntervalCertificate
