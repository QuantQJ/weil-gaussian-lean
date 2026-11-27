import Mathlib

/-!
# Absolute Gaussian-Moebius tails

The proof uses a cubic majorant and elementary telescoping sums.
No hypothesis on zeta zeros or cancellation of Moebius signs is used.
-/

noncomputable section
open scoped BigOperators
open scoped Topology
open Finset Filter Asymptotics

namespace FleetMollifierTail

def kernel (b α x : ℝ) : ℝ :=
  2 * Real.exp (-Real.log x / 2 - b * (Real.log x) ^ 2) *
    Real.cos (α * Real.log x)

/-- The inner sum starts at n = 2; the omitted n = 1 term is zero. -/
def inner (b α : ℝ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, Real.log (n + 2) * kernel b α ((m : ℝ) * (n + 2))

def envelope (b : ℝ) : ℝ := 2 * Real.exp (25 / (16 * b))

lemma envelope_pos (b : ℝ) : 0 < envelope b := by
  unfold envelope
  positivity

lemma gaussian_cubic_exponent (b t : ℝ) (hb : 0 < b) :
    -t / 2 - b * t ^ 2 ≤ 25 / (16 * b) - 3 * t := by
  have hs := sq_nonneg (4 * b * t - 5)
  have hd : 16 * b * (25 / (16 * b)) = 25 := by
    field_simp
  nlinarith

lemma kernel_cubic (b α x : ℝ) (hb : 0 < b) (hx : 0 < x) :
    |kernel b α x| ≤ envelope b / x ^ 3 := by
  have hc := Real.abs_cos_le_one (α * Real.log x)
  have he := Real.exp_le_exp.mpr (gaussian_cubic_exponent b (Real.log x) hb)
  have hid : Real.exp (25 / (16 * b) - 3 * Real.log x) =
      Real.exp (25 / (16 * b)) / x ^ 3 := by
    rw [Real.exp_sub]
    congr 1
    rw [show (3 : ℝ) * Real.log x = Real.log (x ^ 3) by
      simp]
    exact Real.exp_log (pow_pos hx 3)
  calc
    |kernel b α x| ≤ 2 * Real.exp (-Real.log x / 2 - b * (Real.log x) ^ 2) := by
      unfold kernel
      rw [abs_mul, abs_of_pos (by positivity)]
      nlinarith [Real.exp_pos (-Real.log x / 2 - b * (Real.log x) ^ 2)]
    _ ≤ 2 * Real.exp (25 / (16 * b) - 3 * Real.log x) := by linarith
    _ = envelope b / x ^ 3 := by rw [hid]; unfold envelope; ring

lemma log_cubic_le_telescope (x : ℝ) (hx : 2 ≤ x) :
    Real.log x / x ^ 3 ≤ 1 / (x - 1) - 1 / x := by
  have hp : 0 < x := by linarith
  have hm : 0 < x - 1 := by linarith
  have hl : Real.log x ≤ x := by
    linarith [Real.log_le_sub_one_of_pos hp]
  calc
    Real.log x / x ^ 3 ≤ x / x ^ 3 :=
      div_le_div_of_nonneg_right hl (by positivity)
    _ ≤ 1 / (x - 1) - 1 / x := by
      have hid : 1 / (x - 1) - 1 / x = 1 / (x * (x - 1)) := by
        field_simp
        ring
      rw [hid]
      apply (div_le_div_iff₀ (pow_pos hp 3) (mul_pos hp hm)).2
      nlinarith

lemma reciprocal_telescope (K : ℕ) :
    (∑ n ∈ range K, ((1 : ℝ) / (n + 1) - 1 / (n + 2))) =
      1 - 1 / (K + 1) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

lemma abs_tsum_bound (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, |f n| ≤ C * (1 / (n + 1) - 1 / (n + 2))) :
    Summable f ∧ |∑' n, f n| ≤ C := by
  have hsum : ∀ K, ∑ n ∈ range K, |f n| ≤ C := by
    intro K
    calc
      _ ≤ ∑ n ∈ range K, C * (1 / (n + 1) - 1 / (n + 2)) :=
        sum_le_sum fun n _ => hf n
      _ = C * (1 - 1 / (K + 1)) := by
        rw [← mul_sum, reciprocal_telescope]
      _ ≤ C := by
        have h : 0 ≤ (1 : ℝ) / (K + 1) := by positivity
        nlinarith
  have habs : Summable (fun n => |f n|) :=
    summable_of_sum_range_le (fun n => abs_nonneg _) hsum
  have hnorm : Summable (fun n => ‖f n‖) := by simpa only [Real.norm_eq_abs] using habs
  refine ⟨hnorm.of_norm, ?_⟩
  have ht := norm_tsum_le_tsum_norm hnorm
  simp only [Real.norm_eq_abs] at ht
  exact ht.trans (Real.tsum_le_of_sum_range_le (fun n => abs_nonneg _) hsum)

lemma inner_summable_and_bound (b α : ℝ) (m : ℕ) (hb : 0 < b) (hm : 1 ≤ m) :
    Summable (fun n : ℕ =>
      Real.log (n + 2) * kernel b α ((m : ℝ) * (n + 2))) ∧
    |inner b α m| ≤ envelope b / (m : ℝ) ^ 3 := by
  have hmp : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have henv := envelope_pos b
  apply abs_tsum_bound _ _ (by positivity)
  intro n
  have hn : (2 : ℝ) ≤ n + 2 := by
    have : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hnp : 0 < (n : ℝ) + 2 := by positivity
  have hlog : 0 ≤ Real.log (n + 2) :=
    Real.log_nonneg (by linarith)
  calc
    _ = Real.log (n + 2) * |kernel b α ((m : ℝ) * (n + 2))| := by
      rw [abs_mul, abs_of_nonneg hlog]
    _ ≤ Real.log (n + 2) * (envelope b / ((m : ℝ) * (n + 2)) ^ 3) :=
      mul_le_mul_of_nonneg_left (kernel_cubic b α _ hb (mul_pos hmp hnp)) hlog
    _ = (envelope b / (m : ℝ) ^ 3) * (Real.log (n + 2) / (n + 2) ^ 3) := by
      field_simp
    _ ≤ (envelope b / (m : ℝ) ^ 3) *
        (1 / (n + 1) - 1 / (n + 2)) := by
      have h := log_cubic_le_telescope (n + 2) hn
      rw [show (n : ℝ) + 2 - 1 = n + 1 by ring] at h
      exact mul_le_mul_of_nonneg_left h (by positivity)

lemma cubic_le_square_difference (x : ℝ) (hx : 1 ≤ x) :
    1 / (x + 1) ^ 3 ≤ 1 / x ^ 2 - 1 / (x + 1) ^ 2 := by
  have hp : 0 < x := by linarith
  have hq : 0 < x + 1 := by linarith
  have hid : 1 / x ^ 2 - 1 / (x + 1) ^ 2 =
      (2 * x + 1) / (x ^ 2 * (x + 1) ^ 2) := by
    field_simp
    ring
  rw [hid]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (sq_nonneg (x + 1))]

lemma square_telescope (M L : ℕ) :
    (∑ k ∈ range L,
      ((1 : ℝ) / (M + k) ^ 2 - 1 / (M + k + 1) ^ 2)) =
      1 / (M : ℝ) ^ 2 - 1 / (M + L) ^ 2 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

lemma finite_cubic_tail (M L : ℕ) (hM : 1 ≤ M) :
    (∑ k ∈ range L, (1 : ℝ) / (M + k + 1) ^ 3) ≤
      1 / (M : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ k ∈ range L,
        ((1 : ℝ) / (M + k) ^ 2 - 1 / (M + k + 1) ^ 2) := by
      apply sum_le_sum
      intro k hk
      exact cubic_le_square_difference _ (by
        have : (1 : ℝ) ≤ M := by exact_mod_cast hM
        have : 0 ≤ (k : ℝ) := by positivity
        linarith)
    _ = 1 / (M : ℝ) ^ 2 - 1 / (M + L) ^ 2 := square_telescope M L
    _ ≤ 1 / (M : ℝ) ^ 2 := sub_le_self _ (by positivity)

/-- All bounded coefficients work, not just Moebius. -/
theorem finite_tail_bound (b α : ℝ) (a : ℕ → ℝ) (M L : ℕ)
    (hb : 0 < b) (hM : 1 ≤ M) (ha : ∀ m, |a m| ≤ 1) :
    |∑ k ∈ range L, a (M + k + 1) * inner b α (M + k + 1)| ≤
      envelope b / (M : ℝ) ^ 2 := by
  have henv := (envelope_pos b).le
  calc
    _ ≤ ∑ k ∈ range L, |a (M + k + 1) * inner b α (M + k + 1)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range L, envelope b / (M + k + 1 : ℝ) ^ 3 := by
      apply sum_le_sum
      intro k hk
      rw [abs_mul]
      calc
        _ ≤ 1 * |inner b α (M + k + 1)| :=
          mul_le_mul_of_nonneg_right (ha _) (abs_nonneg _)
        _ ≤ envelope b / (M + k + 1 : ℝ) ^ 3 := by
          simpa using (inner_summable_and_bound b α (M + k + 1) hb (by omega)).2
    _ = envelope b * ∑ k ∈ range L, (1 : ℝ) / (M + k + 1) ^ 3 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      ring
    _ ≤ envelope b * (1 / (M : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (finite_cubic_tail M L hM) henv
    _ = envelope b / (M : ℝ) ^ 2 := by ring

lemma moebius_abs_le (m : ℕ) :
    |(ArithmeticFunction.moebius m : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := m))

theorem moebius_finite_tail_bound (b α : ℝ) (M L : ℕ)
    (hb : 0 < b) (hM : 1 ≤ M) :
    |∑ k ∈ range L, (ArithmeticFunction.moebius (M + k + 1) : ℝ) *
      inner b α (M + k + 1)| ≤ envelope b / (M : ℝ) ^ 2 :=
  finite_tail_bound b α (fun m => (ArithmeticFunction.moebius m : ℝ))
    M L hb hM moebius_abs_le

theorem moebius_interval_tail_bound (b α : ℝ) (M N : ℕ)
    (hb : 0 < b) (hM : 1 ≤ M) :
    |∑ m ∈ Ioc M N, (ArithmeticFunction.moebius m : ℝ) * inner b α m| ≤
      envelope b / (M : ℝ) ^ 2 := by
  rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range]
  simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    using moebius_finite_tail_bound b α M (N - M) hb hM

lemma envelope_at_half_cutoff (b M : ℝ) (hb : 0 < b)
    (hM : Real.exp (11 / (10 * b)) / 2 ≤ M) :
    envelope b / M ^ 2 ≤ 8 * Real.exp (-51 / (80 * b)) := by
  have hr := Real.exp_pos (11 / (10 * b))
  have hMp : 0 < M := by linarith
  have hs : Real.exp (11 / (10 * b)) ^ 2 ≤ 4 * M ^ 2 := by
    nlinarith [sq_nonneg (2 * M - Real.exp (11 / (10 * b)))]
  have he : Real.exp (25 / (16 * b)) =
      Real.exp (-51 / (80 * b)) * Real.exp (11 / (10 * b)) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    field_simp
    ring
  apply (div_le_iff₀ (sq_pos_of_pos hMp)).2
  unfold envelope
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hs (Real.exp_nonneg (-51 / (80 * b)))]

lemma cutoff_floor_bounds (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    1 ≤ ⌊Real.exp (11 / (10 * b))⌋₊ ∧
    Real.exp (11 / (10 * b)) / 2 ≤ (⌊Real.exp (11 / (10 * b))⌋₊ : ℝ) := by
  have hf : (1 : ℝ) ≤ 11 / (10 * b) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  have hr : (2 : ℝ) ≤ Real.exp (11 / (10 * b)) := by
    linarith [Real.add_one_le_exp (11 / (10 * b))]
  have hM : 1 ≤ ⌊Real.exp (11 / (10 * b))⌋₊ := Nat.le_floor (by linarith)
  refine ⟨hM, ?_⟩
  have hMr : (1 : ℝ) ≤ ⌊Real.exp (11 / (10 * b))⌋₊ := by exact_mod_cast hM
  have hfloor := Nat.lt_floor_add_one (Real.exp (11 / (10 * b)))
  linarith

/-- Uniform in the upper endpoint and in alpha, including the real cutoff's rounding. -/
theorem exponential_interval_tail (b α : ℝ) (N : ℕ)
    (hb : 0 < b) (hb1 : b ≤ 1) :
    |∑ m ∈ Ioc ⌊Real.exp (11 / (10 * b))⌋₊ N,
      (ArithmeticFunction.moebius m : ℝ) * inner b α m| ≤
      8 * Real.exp (-51 / (80 * b)) := by
  have hc := cutoff_floor_bounds b hb hb1
  exact (moebius_interval_tail_bound b α _ N hb hc.1).trans
    (envelope_at_half_cutoff b _ hb hc.2)

lemma sqrt_exponential_cutoff (b : ℝ) (hb : 0 < b) :
    Real.sqrt (Real.exp (11 / (5 * b))) = Real.exp (11 / (10 * b)) := by
  have he : Real.exp (11 / (5 * b)) = Real.exp (11 / (10 * b)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
    ring
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The user's exact sqrt(N) < m <= N window, with N = exp(2.2/b). -/
def windowTail (b α : ℝ) : ℝ :=
  ∑ m ∈ Ioc ⌊Real.sqrt (Real.exp (11 / (5 * b)))⌋₊
      ⌊Real.exp (11 / (5 * b))⌋₊,
    (ArithmeticFunction.moebius m : ℝ) * inner b α m

theorem windowTail_exponential (b α : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    |windowTail b α| ≤ 8 * Real.exp (-51 / (80 * b)) := by
  unfold windowTail
  rw [sqrt_exponential_cutoff b hb]
  exact exponential_interval_tail b α _ hb hb1

theorem windowTail_normalized (b α : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    |windowTail b α| ≤ 8 * Real.sqrt (Real.pi / b) := by
  have hs : 1 ≤ Real.sqrt (Real.pi / b) := by
    apply Real.one_le_sqrt.mpr
    apply (le_div_iff₀ hb).2
    linarith [Real.two_le_pi]
  have he : Real.exp (-51 / (80 * b)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have h := windowTail_exponential b α hb hb1
  nlinarith

/-- Standard Big-O formulation as b approaches zero through positive values.
The explicit preceding theorem has the same constant 8 for every alpha. -/
theorem windowTail_isBigO (α : ℝ) :
    (fun b => windowTail b α) =O[𝓝[>] (0 : ℝ)]
      (fun b => Real.sqrt (Real.pi / b)) := by
  apply Asymptotics.IsBigO.of_bound 8
  have hu : ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ), b < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hu] with b hb hb1
  have h := windowTail_normalized b α hb hb1.le
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using h

/-- Identifies the exponential definition with the usual Gaussian kernel. -/
theorem kernel_eq_rpow (b α x : ℝ) (hx : 0 < x) :
    kernel b α x =
      2 * x ^ (-(1 / 2 : ℝ)) * Real.exp (-b * (Real.log x) ^ 2) *
        Real.cos (α * Real.log x) := by
  rw [kernel, Real.rpow_def_of_pos hx]
  rw [show -Real.log x / 2 - b * (Real.log x) ^ 2 =
      Real.log x * (-(1 / 2 : ℝ)) + (-b * (Real.log x) ^ 2) by ring,
    Real.exp_add]
  ring

#print axioms kernel_cubic
#print axioms inner_summable_and_bound
#print axioms moebius_finite_tail_bound
#print axioms windowTail_exponential
#print axioms windowTail_normalized
#print axioms windowTail_isBigO
#print axioms kernel_eq_rpow

end FleetMollifierTail
