import FleetHeadContourConverse

/-!
# Attempts on an unconditional window rate below `1/8`

The window is `W(b, α) = headWindow b α = ∫ ‖M_{cut b}(1/2+it)‖² e^{-(t-α)²/(4b)} dt`, `cut b = ⌊e^{11/(10b)}⌋`.
`FleetHeadContour.zeros_in_strip_of_window_rate` turns a rate `W ≤ C e^{c/b}` into `|Re ρ − 1/2| ≤ √(2c)`; the
unconditional rate `11/10` is `FleetHeadContour.windowRate_eleven_tenths` (FleetHeadContourConverse).
This module proves the unconditional statements met while attacking `c < 1/8`:

* `Wg_le_double_sum`  : Gaussian mean-value inequality, `W_N(β, A) ≤ √(4πβ) Σ_{m,n ≤ N} |v_m||v_n| e^{-β(log m − log n)²}`,
                        `v_m = μ(m)/√m`, uniformly in the centre `A`.
* `Wg_le_wide`        : `W_N(β, A) ≤ √(4πβ) (1 + log N + 4N e^{-β/N²})` (diagonal plus separated off-diagonal).
* `avg_Wg`            : the Gaussian α-average of narrow windows is a wide window,
                        `∫ W_N(b, α) e^{-(α-A)²/4B} dα = √(π·4bB/(b+B)) · W_N(b+B, A)`.
* `window_rate_zero_on_average` : for `B ≥ N² log(4N)` (`N = cut b`), the normalised α-average of `W(b, ·)` is
                        `≤ √(4πb)(2 + 11/(10b))`: rate `0` on average over α-ranges of width `≳ e^{1.1/b}`.
* `moebius_eq_of_le_sq`, `Mpoly_sq_eq` : the squaring identity `μ = 2μ_N − 1 * μ_N * μ_N` on `n ≤ N²`, hence
                        `M_{N²}(w) = 2 M_N(w) − Σ_{n ≤ N²} (1 * μ_N * μ_N)(n) n^{-w}` (relates the window at `b` and `b/2`).
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real
open OffLineDetection Reduction ZeroSumLimit GaussianTest

namespace FleetStripAttempt

open FleetHeadContour

/-- **`Σ_{1 ≤ m ≤ N} m^{-1/2} ≤ 2√N`** (from `FleetHeadContour.two_sqrt_step`). -/
lemma sum_rsqrt_le (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), (if m = 0 then (0 : ℝ) else 1 / Real.sqrt m) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    have h := two_sqrt_step n
    have hr : ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt ((n : ℝ) + 1) := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    rw [hr] at h
    push_cast
    linarith

/-! ## Part 2: the Gaussian mean-value theorem and the α-averaged window -/

/-- The window of `M_N` at Gaussian width `β` and centre `A`. -/
def Wg (N : ℕ) (β A : ℝ) : ℝ :=
  ∫ t : ℝ, ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - A) ^ 2 / (4 * β))

/-- `v m = μ(m)/√m`. -/
def v (m : ℕ) : ℝ := (ArithmeticFunction.moebius m : ℝ) / Real.sqrt m

lemma term_eq (m : ℕ) (t : ℝ) :
    (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + t * I))
      = (v m : ℂ) * cexp (-(((0 : ℝ) : ℂ) + t * I) * (Real.log m : ℂ)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [v]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Complex.cpow_def_of_ne_zero hmc, show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log hm0.le]
  have hs : Real.sqrt (m : ℝ) = Real.exp (Real.log m / 2) := by
    rw [Real.exp_half, Real.exp_log hm0]
  have hv : (v m : ℂ) = (ArithmeticFunction.moebius m : ℂ) * cexp (-(Real.log m : ℂ) / 2) := by
    unfold v
    rw [hs, div_eq_mul_inv, ← Real.exp_neg]
    push_cast
    ring_nf
  rw [hv, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma conj_term (m : ℕ) (t : ℝ) :
    (starRingEnd ℂ) ((v m : ℂ) * cexp (-(((0 : ℝ) : ℂ) + t * I) * (Real.log m : ℂ)))
      = (v m : ℂ) * cexp ((((0 : ℝ) : ℂ) + t * I) * (Real.log m : ℂ)) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  rw [map_mul, map_neg, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.conj_I]
  push_cast
  ring

lemma Mpoly_half_eq (N : ℕ) (t : ℝ) :
    Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)
      = ∑ m ∈ Finset.range (N + 1), (v m : ℂ) * cexp (-(((0 : ℝ) : ℂ) + t * I) * (Real.log m : ℂ)) := by
  unfold Mpoly
  exact Finset.sum_congr rfl fun m _ => term_eq m t

/-- `‖M_N(1/2+it)‖²` as a double sum. -/
lemma normSq_Mpoly_half (N : ℕ) (t : ℝ) :
    ((‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 1),
          ((v m * v n : ℝ) : ℂ) * cexp (-(((0 : ℝ) : ℂ) + t * I) * ((Real.log m - Real.log n : ℝ) : ℂ)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', Mpoly_half_eq, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [conj_term]
  have : cexp (-(((0 : ℝ) : ℂ) + t * I) * (Real.log m : ℂ)) * cexp ((((0 : ℝ) : ℂ) + t * I) * (Real.log n : ℂ))
      = cexp (-(((0 : ℝ) : ℂ) + t * I) * ((Real.log m : ℂ) - (Real.log n : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; ring
  calc (v m : ℂ) * cexp (-(((0 : ℝ) : ℂ) + t * I) * (Real.log m : ℂ))
        * ((v n : ℂ) * cexp ((((0 : ℝ) : ℂ) + t * I) * (Real.log n : ℂ)))
      = (v m : ℂ) * (v n : ℂ) * (cexp (-(((0 : ℝ) : ℂ) + t * I) * (Real.log m : ℂ))
          * cexp ((((0 : ℝ) : ℂ) + t * I) * (Real.log n : ℂ))) := by ring
    _ = _ := by rw [this]; push_cast; ring

/-- The real Gaussian as a complex quadratic exponential. -/
lemma gauss_ofReal (β A t : ℝ) :
    ((Real.exp (-(t - A) ^ 2 / (4 * β)) : ℝ) : ℂ)
      = cexp ((-(A : ℂ) * I + t * I) ^ 2 / (4 * β)) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Gaussian Fourier coefficient**: `‖∫ e^{-(t-A)²/4β} e^{-itL} dt‖ = √(4πβ) e^{-βL²}`. -/
lemma norm_gauss_fourier {β : ℝ} (hβ : 0 < β) (A L : ℝ) :
    ‖∫ t : ℝ, cexp (-(((0 : ℝ) : ℂ) + t * I) * (L : ℂ)) * ((Real.exp (-(t - A) ^ 2 / (4 * β)) : ℝ) : ℂ)‖
      = Real.sqrt (4 * π * β) * Real.exp (-β * L ^ 2) := by
  have e : (fun t : ℝ => cexp (-(((0 : ℝ) : ℂ) + t * I) * (L : ℂ)) * ((Real.exp (-(t - A) ^ 2 / (4 * β)) : ℝ) : ℂ))
      = fun t : ℝ => cexp ((-(A : ℂ) * I + t * I) ^ 2 / (4 * β)) * cexp (-(((0 : ℝ) : ℂ) + t * I) * L) := by
    funext t; rw [gauss_ofReal, mul_comm]
  rw [e, integral_quad hβ (-(A : ℂ) * I) 0 L, norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  congr 2
  have hL : ((L : ℂ) ^ 2).re = L ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
  simp [hL]

lemma integrable_gauss_fourier {β : ℝ} (hβ : 0 < β) (A L : ℝ) :
    Integrable (fun t : ℝ => cexp (-(((0 : ℝ) : ℂ) + t * I) * (L : ℂ)) * ((Real.exp (-(t - A) ^ 2 / (4 * β)) : ℝ) : ℂ)) := by
  have e : (fun t : ℝ => cexp (-(((0 : ℝ) : ℂ) + t * I) * (L : ℂ)) * ((Real.exp (-(t - A) ^ 2 / (4 * β)) : ℝ) : ℂ))
      = fun t : ℝ => cexp ((-(A : ℂ) * I + t * I) ^ 2 / (4 * β)) * cexp (-(((0 : ℝ) : ℂ) + t * I) * L) := by
    funext t; rw [gauss_ofReal, mul_comm]
  rw [e]; exact integrable_quad hβ _ 0 L

/-- **Gaussian mean-value inequality**:
`W_N(β, A) ≤ √(4πβ) Σ_{m,n ≤ N} |v m| |v n| e^{-β (log m − log n)²}`, uniformly in `A`. -/
theorem Wg_le_double_sum (N : ℕ) {β : ℝ} (hβ : 0 < β) (A : ℝ) :
    Wg N β A ≤ Real.sqrt (4 * π * β) * ∑ m ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 1),
      |v m| * |v n| * Real.exp (-β * (Real.log m - Real.log n) ^ 2) := by
  set g : ℝ → ℝ := fun t => Real.exp (-(t - A) ^ 2 / (4 * β)) with hg
  set F : ℕ → ℕ → ℝ → ℂ := fun m n t => ((v m * v n : ℝ) : ℂ) *
    (cexp (-(((0 : ℝ) : ℂ) + t * I) * ((Real.log m - Real.log n : ℝ) : ℂ)) * ((g t : ℝ) : ℂ)) with hF
  have hFi : ∀ m n, Integrable (F m n) := fun m n =>
    (integrable_gauss_fourier hβ A (Real.log m - Real.log n)).const_mul _
  have hW : ((Wg N β A : ℝ) : ℂ) = ∑ m ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 1), ∫ t, F m n t := by
    unfold Wg
    rw [← integral_complex_ofReal]
    have hpt : ∀ t : ℝ, (((‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - A) ^ 2 / (4 * β)) : ℝ)) : ℂ)
        = ∑ m ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 1), F m n t := by
      intro t
      rw [Complex.ofReal_mul, normSq_Mpoly_half, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [hF, hg]; ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => hFi m n]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_finsetSum _ fun n _ => hFi m n]
  have hnorm : ∀ m n, ‖∫ t, F m n t‖
      = |v m| * |v n| * (Real.sqrt (4 * π * β) * Real.exp (-β * (Real.log m - Real.log n) ^ 2)) := by
    intro m n
    simp only [hF]
    rw [integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      norm_gauss_fourier hβ]
  have h1 : Wg N β A ≤ ‖((Wg N β A : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
  rw [hW] at h1
  refine h1.trans ((norm_sum_le _ _).trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => (norm_sum_le _ _).trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hnorm]; ring


lemma abs_v_le (m : ℕ) : |v m| ≤ (if m = 0 then (0 : ℝ) else 1 / Real.sqrt m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [v]
  simp only [hm.ne', ↓reduceIte]
  unfold v
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right (FleetMollifierTail.moebius_abs_le m) (Real.sqrt_nonneg _)

lemma sum_abs_v_le (N : ℕ) : ∑ m ∈ Finset.range (N + 1), |v m| ≤ 2 * Real.sqrt N :=
  (Finset.sum_le_sum fun m _ => abs_v_le m).trans (sum_rsqrt_le N)

lemma sum_sq_v_le (N : ℕ) : ∑ m ∈ Finset.range (N + 1), |v m| ^ 2 ≤ 1 + Real.log N := by
  have hpt : ∀ m ∈ Finset.range (N + 1), |v m| ^ 2 ≤ (if m = 0 then (0 : ℝ) else 1 / (m : ℝ)) := by
    intro m _
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [v]
    have h := abs_v_le m
    simp only [hm.ne', ↓reduceIte] at h ⊢
    have h0 : 0 ≤ |v m| := abs_nonneg _
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    calc |v m| ^ 2 ≤ (1 / Real.sqrt m) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = 1 / (m : ℝ) := by rw [div_pow, Real.sq_sqrt hm0.le, one_pow]
  refine (Finset.sum_le_sum hpt).trans ?_
  have hh : ∑ m ∈ Finset.range (N + 1), (if m = 0 then (0 : ℝ) else 1 / (m : ℝ)) = (harmonic N : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero, ↓reduceIte, add_zero, harmonic]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_div]
  rw [hh]
  exact harmonic_le_one_add_log N

/-- Distinct `m, n ≤ N` have `|log m − log n| ≥ 1/N`. -/
lemma log_gap {N m n : ℕ} (hn : 1 ≤ n) (hnm : n < m) (hmN : m ≤ N) :
    1 / (N : ℝ) ≤ Real.log m - Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm1 : (n : ℝ) + 1 ≤ m := by exact_mod_cast hnm
  have hN : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have h1 : Real.log ((n : ℝ) / ((n : ℝ) + 1)) ≤ (n : ℝ) / ((n : ℝ) + 1) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hn0.ne' (by positivity)] at h1
  have h2 : Real.log ((n : ℝ) + 1) ≤ Real.log m := Real.log_le_log (by positivity) hm1
  have h3 : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by field_simp; ring
  have h4 : 1 / (N : ℝ) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (hm1.trans hN)
  linarith

lemma sq_log_gap {N m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) (hmN : m ≤ N) (hnN : n ≤ N) :
    1 / (N : ℝ) ^ 2 ≤ (Real.log m - Real.log n) ^ 2 := by
  have hN : (0 : ℝ) < N := by have : 1 ≤ N := hm.trans hmN; exact_mod_cast this
  rcases lt_or_gt_of_ne hmn with h | h
  · have g := log_gap hm h hnN
    have g0 : 0 ≤ 1 / (N : ℝ) := by positivity
    rw [show (Real.log m - Real.log n) ^ 2 = (Real.log n - Real.log m) ^ 2 by ring, one_div, ← inv_pow,
      ← one_div]
    exact pow_le_pow_left₀ g0 g 2
  · have g := log_gap hn h hmN
    have g0 : 0 ≤ 1 / (N : ℝ) := by positivity
    rw [one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ g0 g 2

/-- **Wide-window bound** (Gaussian mean-value theorem):
`W_N(β, A) ≤ √(4πβ) (1 + log N + 4N e^{-β/N²})` for every centre `A`. -/
theorem Wg_le_wide {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β) (A : ℝ) :
    Wg N β A ≤ Real.sqrt (4 * π * β) * (1 + Real.log N + 4 * N * Real.exp (-β / (N : ℝ) ^ 2)) := by
  refine (Wg_le_double_sum N hβ A).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  set e := Real.exp (-β / (N : ℝ) ^ 2) with he
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ m ∈ Finset.range (N + 1), ∀ n ∈ Finset.range (N + 1),
      |v m| * |v n| * Real.exp (-β * (Real.log m - Real.log n) ^ 2)
        ≤ (if m = n then |v m| ^ 2 else 0) + |v m| * |v n| * e := by
    intro m hm n hn
    have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hp : 0 ≤ |v m| * |v n| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    by_cases hmn : m = n
    · subst hmn
      simp only [↓reduceIte, sub_self]
      norm_num
      nlinarith [mul_nonneg hp he0]
    · simp only [hmn, ↓reduceIte, zero_add]
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · simp [v]
      rcases Nat.eq_zero_or_pos n with rfl | hn1
      · simp [v]
      have hg := sq_log_gap hm1 hn1 hmn hmN hnN
      have hex : Real.exp (-β * (Real.log m - Real.log n) ^ 2) ≤ e := by
        rw [he, Real.exp_le_exp, neg_div, neg_mul, neg_le_neg_iff, div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hg hβ.le
      exact mul_le_mul_of_nonneg_left hex hp
  calc ∑ m ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 1),
        |v m| * |v n| * Real.exp (-β * (Real.log m - Real.log n) ^ 2)
      ≤ ∑ m ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 1),
          ((if m = n then |v m| ^ 2 else 0) + |v m| * |v n| * e) :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hpt m hm n hn
    _ = ∑ m ∈ Finset.range (N + 1), |v m| ^ 2
          + e * ((∑ m ∈ Finset.range (N + 1), |v m|) * (∑ n ∈ Finset.range (N + 1), |v n|)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq (Finset.range (N + 1)) m, Finset.mul_sum]
        simp only [hm, ↓reduceIte]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        ring
    _ ≤ (1 + Real.log N) + e * ((2 * Real.sqrt N) * (2 * Real.sqrt N)) := by
        have h1 := sum_sq_v_le N
        have h2 := sum_abs_v_le N
        have h0 : 0 ≤ ∑ m ∈ Finset.range (N + 1), |v m| := Finset.sum_nonneg fun m _ => abs_nonneg _
        have he0 : 0 ≤ e := (Real.exp_pos _).le
        have hpp : (∑ m ∈ Finset.range (N + 1), |v m|) * (∑ n ∈ Finset.range (N + 1), |v n|)
            ≤ (2 * Real.sqrt N) * (2 * Real.sqrt N) := mul_le_mul h2 h2 h0 (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hpp he0]
    _ = 1 + Real.log N + 4 * N * e := by
        have : Real.sqrt (N : ℝ) * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
        have e2 : e * ((2 * Real.sqrt N) * (2 * Real.sqrt N)) = 4 * N * e := by
          rw [show (2 * Real.sqrt (N : ℝ)) * (2 * Real.sqrt N) = 4 * (Real.sqrt N * Real.sqrt N) by ring, this]
          ring
        rw [e2]


/-- **Gaussian convolution**: `∫ e^{-(t-α)²/4b} e^{-(α-A)²/4B} dα = √(π · 4bB/(b+B)) e^{-(t-A)²/(4(b+B))}`. -/
lemma gauss_conv {b B : ℝ} (hb : 0 < b) (hB : 0 < B) (t A : ℝ) :
    ∫ α : ℝ, Real.exp (-(t - α) ^ 2 / (4 * b)) * Real.exp (-(α - A) ^ 2 / (4 * B))
      = Real.sqrt (π * (4 * b * B / (b + B))) * Real.exp (-(t - A) ^ 2 / (4 * (b + B))) := by
  set d := 4 * b * B / (b + B) with hd
  have hd0 : 0 < d := by positivity
  set α₀ := (B * t + b * A) / (b + B) with hα₀
  have hpt : ∀ α : ℝ, Real.exp (-(t - α) ^ 2 / (4 * b)) * Real.exp (-(α - A) ^ 2 / (4 * B))
      = Real.exp (-(α - α₀) ^ 2 / d) * Real.exp (-(t - A) ^ 2 / (4 * (b + B))) := by
    intro α
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hd, hα₀]
    field_simp
    ring
  simp_rw [hpt]
  rw [integral_mul_const, integral_gauss_scale hd0]

lemma continuous_normSq_Mpoly (N : ℕ) :
    Continuous (fun t : ℝ => ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2) :=
  (((differentiable_Mpoly N).continuous.comp (continuous_line (1 / 2))).norm.pow 2)

lemma normSq_Mpoly_le (N : ℕ) (t : ℝ) : ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 ≤ 4 * N := by
  have h := norm_Mpoly_half_le N t
  have h0 := norm_nonneg (Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I))
  have hs : (2 * Real.sqrt N) ^ 2 = 4 * (N : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [← hs]; exact pow_le_pow_left₀ h0 h 2

/-- **The α-average of narrow windows is a wide window**:
`∫ W_N(b, α) e^{-(α-A)²/4B} dα = √(π · 4bB/(b+B)) · W_N(b+B, A)`. -/
theorem avg_Wg {b B : ℝ} (hb : 0 < b) (hB : 0 < B) (N : ℕ) (A : ℝ) :
    ∫ α : ℝ, Wg N b α * Real.exp (-(α - A) ^ 2 / (4 * B))
      = Real.sqrt (π * (4 * b * B / (b + B))) * Wg N (b + B) A := by
  set f : ℝ → ℝ := fun t => ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 with hf
  set F : ℝ → ℝ → ℝ := fun α t =>
    f t * Real.exp (-(t - α) ^ 2 / (4 * b)) * Real.exp (-(α - A) ^ 2 / (4 * B)) with hF
  have hfc : Continuous f := continuous_normSq_Mpoly N
  set G : ℝ × ℝ → ℝ := fun p =>
    4 * N * Real.exp (-(p.2 - p.1) ^ 2 / (4 * b)) * Real.exp (-(p.1 - A) ^ 2 / (4 * B)) with hG
  have hGc : Continuous G := by simp only [hG]; fun_prop
  have hGi : Integrable G (volume.prod volume) := by
    rw [integrable_prod_iff hGc.aestronglyMeasurable]
    constructor
    · refine ae_of_all _ fun α => ?_
      simp only [hG]
      exact ((integrable_gauss_scale (d := 4 * b) (by positivity) α).const_mul (4 * N)).mul_const _
    · have e : (fun α : ℝ => ∫ t : ℝ, ‖G (α, t)‖)
          = fun α => (4 * N * Real.sqrt (π * (4 * b))) * Real.exp (-(α - A) ^ 2 / (4 * B)) := by
        funext α
        have hnn : ∀ t, ‖G (α, t)‖ = G (α, t) := fun t => by
          rw [Real.norm_eq_abs, abs_of_nonneg]; simp only [hG]; positivity
        simp_rw [hnn]
        simp only [hG]
        rw [integral_mul_const, integral_const_mul, integral_gauss_scale (by positivity)]
      rw [e]
      exact (integrable_gauss_scale (d := 4 * B) (by positivity) A).const_mul _
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine Integrable.mono' hGi ?_ (ae_of_all _ fun p => ?_)
    · have : Continuous (Function.uncurry F) := by
        simp only [hF]
        exact ((hfc.comp continuous_snd).mul (by fun_prop)).mul (by fun_prop)
      exact this.aestronglyMeasurable
    · simp only [Function.uncurry, hF, hG]
      have h1 := normSq_Mpoly_le N p.2
      have hf0 : 0 ≤ f p.2 := by simp only [hf]; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hE := (Real.exp_pos (-(p.2 - p.1) ^ 2 / (4 * b))).le
      have hE' := (Real.exp_pos (-(p.1 - A) ^ 2 / (4 * B))).le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hE) hE'
  have hL : ∀ α : ℝ, Wg N b α * Real.exp (-(α - A) ^ 2 / (4 * B)) = ∫ t : ℝ, F α t := by
    intro α
    unfold Wg
    rw [← integral_mul_const]
  simp_rw [hL]
  rw [integral_integral_swap hFi]
  have hR : ∀ t : ℝ, ∫ α : ℝ, F α t
      = Real.sqrt (π * (4 * b * B / (b + B))) * (f t * Real.exp (-(t - A) ^ 2 / (4 * (b + B)))) := by
    intro t
    simp only [hF]
    simp_rw [mul_assoc]
    rw [integral_const_mul, gauss_conv hb hB]
    ring_nf
  simp_rw [hR]
  rw [integral_const_mul]
  rfl

/-- **The window has rate `0` on α-average.** For every centre `A` and every `B > 0`,
`(1/√(4πB)) ∫ W_N(b, α) e^{-(α-A)²/4B} dα ≤ √(4πb) (1 + log N + 4N e^{-(b+B)/N²})`. -/
theorem avg_window_le {N : ℕ} (hN : 1 ≤ N) {b B : ℝ} (hb : 0 < b) (hB : 0 < B) (A : ℝ) :
    (∫ α : ℝ, Wg N b α * Real.exp (-(α - A) ^ 2 / (4 * B))) / Real.sqrt (4 * π * B)
      ≤ Real.sqrt (4 * π * b) * (1 + Real.log N + 4 * N * Real.exp (-(b + B) / (N : ℝ) ^ 2)) := by
  rw [avg_Wg hb hB N A]
  have hW := Wg_le_wide hN (β := b + B) (by positivity) A
  have hsB : 0 < Real.sqrt (4 * π * B) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_iff₀ hsB]
  have key : Real.sqrt (π * (4 * b * B / (b + B))) * Real.sqrt (4 * π * (b + B))
      = Real.sqrt (4 * π * b) * Real.sqrt (4 * π * B) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  set K := 1 + Real.log N + 4 * N * Real.exp (-(b + B) / (N : ℝ) ^ 2)
  calc Real.sqrt (π * (4 * b * B / (b + B))) * Wg N (b + B) A
      ≤ Real.sqrt (π * (4 * b * B / (b + B))) * (Real.sqrt (4 * π * (b + B)) * K) :=
        mul_le_mul_of_nonneg_left hW (Real.sqrt_nonneg _)
    _ = Real.sqrt (4 * π * b) * K * Real.sqrt (4 * π * B) := by
        rw [← mul_assoc, key]; ring

/-- **Rate `0` on average for the actual window.** With `N = cut b`, `0 < b ≤ 1` and an averaging width
`B ≥ N² log(4N)`, the Gaussian α-average of `W(b, α)` around any centre `A` is at most
`√(4πb) (2 + 11/(10b))`: polynomial in `1/b`, i.e. window rate `0` on average. -/
theorem window_rate_zero_on_average {b B : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hB : (FleetFiniteHeadRH.cut b : ℝ) ^ 2 * Real.log (4 * FleetFiniteHeadRH.cut b) ≤ B) (A : ℝ) :
    (∫ α : ℝ, headWindow b α * Real.exp (-(α - A) ^ 2 / (4 * B)))
      / Real.sqrt (4 * π * B) ≤ Real.sqrt (4 * π * b) * (2 + 11 / (10 * b)) := by
  set N := FleetFiniteHeadRH.cut b with hNdef
  have hN : 1 ≤ N := cut_pos hb hb1
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog4 : 0 < Real.log (4 * (N : ℝ)) := Real.log_pos (by linarith)
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  have h := avg_window_le hN hb hB0 A
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  have hlogN := log_cut_le hb hb1
  have hexp : 4 * (N : ℝ) * Real.exp (-(b + B) / (N : ℝ) ^ 2) ≤ 1 := by
    have h1 : -(b + B) / (N : ℝ) ^ 2 ≤ -Real.log (4 * N) := by
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
      nlinarith
    have h2 : Real.exp (-(b + B) / (N : ℝ) ^ 2) ≤ Real.exp (-Real.log (4 * N)) := Real.exp_le_exp.mpr h1
    rw [Real.exp_neg, Real.exp_log (by positivity)] at h2
    have h4 : 0 < 4 * (N : ℝ) := by positivity
    calc 4 * (N : ℝ) * Real.exp (-(b + B) / (N : ℝ) ^ 2) ≤ 4 * (N : ℝ) * (4 * (N : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left h2 h4.le
      _ = 1 := mul_inv_cancel₀ h4.ne'
  linarith


/-! ## Part 3: the squaring identity for truncated Möbius polynomials -/

/-- The Möbius function truncated to `n ≤ N`, as an arithmetic function. -/
def muT (N : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≤ N then ArithmeticFunction.moebius n else 0, by simp⟩

lemma muT_apply (N n : ℕ) : muT N n = if n ≤ N then ArithmeticFunction.moebius n else 0 := rfl

/-- `δ − ζ * μ_N` vanishes on `n ≤ N`. -/
lemma one_sub_zeta_muT_apply {N n : ℕ} (hn : n ≤ N) :
    ((1 : ArithmeticFunction ℤ) - (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * muT N) n = 0 := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
    ArithmeticFunction.coe_zeta_mul_apply]
  have h : ∑ i ∈ n.divisors, muT N i = ∑ i ∈ n.divisors, ArithmeticFunction.moebius i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [muT_apply, if_pos ((Nat.divisor_le hi).trans hn)]
  rw [h, ← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_moebius]
  ring

/-- `(δ − ζ * μ_N)²` vanishes on `n ≤ N²`. -/
lemma sq_one_sub_zeta_muT_apply {N n : ℕ} (hn : n ≤ N ^ 2) :
    (((1 : ArithmeticFunction ℤ) - (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * muT N)
      * ((1 : ArithmeticFunction ℤ) - (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * muT N)) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  by_cases h1 : x.1 ≤ N
  · rw [one_sub_zeta_muT_apply h1, zero_mul]
  · have h2 : x.2 ≤ N := by
      by_contra h2
      push Not at h1 h2
      have : (N + 1) * (N + 1) ≤ x.1 * x.2 := Nat.mul_le_mul h1 h2
      nlinarith [hx.1]
    rw [one_sub_zeta_muT_apply h2, mul_zero]

/-- **The squaring identity.** For `n ≤ N²`,
`μ(n) = 2 μ_N(n) − (1 * μ_N * μ_N)(n)` (`μ_N` = Möbius truncated to `≤ N`, `1` = the constant function). -/
theorem moebius_eq_of_le_sq {N n : ℕ} (hn : n ≤ N ^ 2) :
    ArithmeticFunction.moebius n
      = 2 * muT N n - ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) * muT N * muT N) n := by
  set Z : ArithmeticFunction ℤ := (ArithmeticFunction.zeta : ArithmeticFunction ℤ)
  set m : ArithmeticFunction ℤ := ArithmeticFunction.moebius
  set f : ArithmeticFunction ℤ := 1 - Z * muT N
  have hmz : m * Z = 1 := ArithmeticFunction.moebius_mul_coe_zeta
  have hid : m * (f * f) = m - (muT N + muT N) + Z * muT N * muT N := by
    simp only [f]
    linear_combination (-(muT N + muT N) + Z * muT N * muT N) * hmz
  have hz : (m * (f * f)) n = 0 := by
    rw [ArithmeticFunction.mul_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have hle : x.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hx'.2) ⟨x.1, by rw [← hx'.1]; ring⟩
    rw [sq_one_sub_zeta_muT_apply (hle.trans hn), mul_zero]
  rw [hid, sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply, ArithmeticFunction.add_apply] at hz
  linarith

/-- **The squaring identity for the window polynomial.** For every `w`,
`M_{N²}(w) = 2 M_N(w) − Σ_{n ≤ N²} (1 * μ_N * μ_N)(n) n^{-w}`. -/
theorem Mpoly_sq_eq (N : ℕ) (w : ℂ) :
    Mpoly (N ^ 2) w = 2 * Mpoly N w - ∑ n ∈ Finset.range (N ^ 2 + 1),
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℤ) * muT N * muT N) n : ℤ) : ℂ) * (n : ℂ) ^ (-w) := by
  have hsub : Finset.range (N + 1) ⊆ Finset.range (N ^ 2 + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    nlinarith
  have hT : ∑ n ∈ Finset.range (N ^ 2 + 1), ((muT N n : ℤ) : ℂ) * (n : ℂ) ^ (-w) = Mpoly N w := by
    unfold Mpoly
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [muT_apply, if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
    · intro n _ hn
      rw [Finset.mem_range, not_lt] at hn
      rw [muT_apply, if_neg (by omega)]
      simp
  rw [← hT, Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold Mpoly
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [moebius_eq_of_le_sq (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
  push_cast
  ring

end FleetStripAttempt
