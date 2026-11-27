import FleetPrimeOnlyRH

/-!
# The prime sum through `Λ = μ ∗ log`: Möbius outside, a smooth sum inside

`moebius_mul_log_eq_vonMangoldt` (`μ ∗ log = Λ`) regroups the Gaussian-weighted prime sum by
`n = m·k`, keeping the weight at `log(mk) = log m + log k`:

  `primeSumSym b α = Σ_{m ≥ 1} μ(m) m^{-1/2} · I_b(α, log m)`,
  `I_b(α, v) = Σ_{k ≥ 1} log k · k^{-1/2} (g(log k + v) + g(−(log k + v)))`, `g = gauss b α`.

`I_b` runs over all integers `k`: no primes and no zeros enter it. The rearrangement is absolutely
convergent because `e^{-b(log m + log k)²} ≤ e^{-b log² m} e^{-b log² k}`. This is an exact rewriting:
all arithmetic now sits in the Möbius sum, which must cancel the exponentially large pole part
carried by the `I_b(α, log m)`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open scoped Real ArithmeticFunction ArithmeticFunction.Moebius
open GaussianTest FleetPrimeSideConsequences FleetPrimeOnlyRH

namespace FleetMoebiusSmoothDecomposition

/-- The smooth inner sum over all integers `k`. -/
def Ismooth (b α v : ℝ) : ℂ :=
  ∑' k : ℕ, (Real.log k : ℂ) * (k : ℂ) ^ (-(1 / 2) : ℂ)
    * (gauss b α (Real.log k + v) + gauss b α (-(Real.log k + v)))

/-- The symmetric weight `w(n) = n^{-1/2} (g(log n) + g(−log n))`. -/
def w (b α : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ (-(1 / 2) : ℂ) * (gauss b α (Real.log n) + gauss b α (-Real.log n))

lemma w_zero (b α : ℝ) : w b α 0 = 0 := by
  simp [w, Complex.zero_cpow (by norm_num : (-(1 / 2) : ℂ) ≠ 0)]

lemma norm_w_le (b α : ℝ) (n : ℕ) : ‖w b α n‖ ≤ 2 * Real.exp (-b * Real.log n ^ 2) := by
  unfold w
  rw [norm_mul]
  have hg : ‖gauss b α (Real.log n) + gauss b α (-Real.log n)‖ ≤ 2 * Real.exp (-b * Real.log n ^ 2) := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_gauss, norm_gauss, neg_sq]; ring
  calc ‖(n : ℂ) ^ (-(1 / 2) : ℂ)‖ * ‖gauss b α (Real.log n) + gauss b α (-Real.log n)‖
      ≤ 1 * (2 * Real.exp (-b * Real.log n ^ 2)) :=
        mul_le_mul (GaussianTraceFormula.norm_natCast_cpow_neg_half_le n) hg (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

lemma summable_log_gauss {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℕ => Real.log n * Real.exp (-b * Real.log n ^ 2)) := by
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => 1 / (n : ℝ) ^ 2)
    (Real.summable_one_div_nat_pow.mpr one_lt_two) ?_
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (3 / b)), eventually_ge_atTop 1]
    with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hL0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hL : Real.log n ≤ (n : ℝ) := by linarith [Real.log_le_sub_one_of_pos hn0]
  have h3 : 3 * Real.log n ≤ b * (Real.log n) ^ 2 := by
    have : 3 / b ≤ Real.log n := hn
    rw [div_le_iff₀ hb] at this
    nlinarith
  have hexp3 : Real.exp ((3 : ℕ) * Real.log n) = (n : ℝ) ^ 3 := by
    rw [Real.exp_nat_mul, Real.exp_log hn0]
  push_cast at hexp3
  have hexp : Real.exp (-b * (Real.log n) ^ 2) ≤ 1 / (n : ℝ) ^ 3 := by
    calc Real.exp (-b * (Real.log n) ^ 2) ≤ Real.exp (-(3 * Real.log n)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 / (n : ℝ) ^ 3 := by rw [Real.exp_neg, hexp3, one_div]
  rw [Real.norm_eq_abs, _root_.abs_of_nonneg (mul_nonneg hL0 (Real.exp_pos _).le)]
  calc Real.log n * Real.exp (-b * (Real.log n) ^ 2) ≤ (n : ℝ) * (1 / (n : ℝ) ^ 3) :=
        mul_le_mul hL hexp (Real.exp_pos _).le hn0.le
    _ = 1 / (n : ℝ) ^ 2 := by field_simp

lemma summable_gauss {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℕ => Real.exp (-b * Real.log n ^ 2)) := by
  refine Summable.of_norm_bounded_eventually_nat (summable_log_gauss hb) ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have h1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [Real.norm_eq_abs, _root_.abs_of_nonneg (Real.exp_pos _).le]
  have := Real.exp_pos (-b * Real.log n ^ 2)
  nlinarith

/-- The double-sum term `μ(m) log k · w(mk)`. -/
def F (b α : ℝ) (p : ℕ × ℕ) : ℂ :=
  ((μ p.1 : ℤ) : ℂ) * (Real.log p.2 : ℂ) * w b α (p.1 * p.2)

lemma norm_F_le {b : ℝ} (hb : 0 < b) (α : ℝ) (p : ℕ × ℕ) :
    ‖F b α p‖ ≤ 2 * (Real.exp (-b * Real.log p.1 ^ 2) *
      (Real.log p.2 * Real.exp (-b * Real.log p.2 ^ 2))) := by
  obtain ⟨m, k⟩ := p
  simp only [F]
  rcases Nat.eq_zero_or_pos (m * k) with h0 | hpos
  · rw [h0, w_zero]; simp; positivity
  have hm : 0 < m := Nat.pos_of_mul_pos_right hpos
  have hk : 0 < k := Nat.pos_of_mul_pos_left hpos
  rw [norm_mul, norm_mul]
  have hμ : ‖((μ m : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hl : ‖(Real.log k : ℂ)‖ = Real.log k := by
    rw [Complex.norm_real, Real.norm_eq_abs, _root_.abs_of_nonneg (Real.log_natCast_nonneg k)]
  rw [hl]
  have hLm := Real.log_natCast_nonneg m
  have hLk := Real.log_natCast_nonneg k
  have hlogmk : Real.log ((m * k : ℕ) : ℝ) = Real.log m + Real.log k := by
    push_cast; exact Real.log_mul (by positivity) (by positivity)
  have hw := norm_w_le b α (m * k)
  rw [hlogmk] at hw
  have he : Real.exp (-b * (Real.log m + Real.log k) ^ 2)
      ≤ Real.exp (-b * Real.log m ^ 2) * Real.exp (-b * Real.log k ^ 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hb.le (mul_nonneg hLm hLk)]
  have hw' : ‖w b α (m * k)‖ ≤ 2 * (Real.exp (-b * Real.log m ^ 2) * Real.exp (-b * Real.log k ^ 2)) :=
    hw.trans (by linarith)
  calc ‖((μ m : ℤ) : ℂ)‖ * Real.log k * ‖w b α (m * k)‖
      ≤ 1 * Real.log k * (2 * (Real.exp (-b * Real.log m ^ 2) * Real.exp (-b * Real.log k ^ 2))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hμ hLk) hw' (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma summable_F {b : ℝ} (hb : 0 < b) (α : ℝ) : Summable (F b α) := by
  have hP : Summable (fun p : ℕ × ℕ => Real.exp (-b * Real.log p.1 ^ 2) *
      (Real.log p.2 * Real.exp (-b * Real.log p.2 ^ 2))) :=
    (summable_gauss hb).mul_of_nonneg (summable_log_gauss hb) (fun _ => (Real.exp_pos _).le)
      (fun _ => mul_nonneg (Real.log_natCast_nonneg _) (Real.exp_pos _).le)
  exact Summable.of_norm_bounded (hP.mul_left 2) (norm_F_le hb α)

/-- The fibre of `(m, k) ↦ mk` over `n` sums to `Λ(n) w(n)`. -/
lemma fibre_sum (b α : ℝ) (n : ℕ) :
    ∑' p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n}), F b α p.val = (Λ n : ℂ) * w b α n := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : ∀ p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}), F b α p.val = 0 := by
      rintro ⟨⟨m, k⟩, hp⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp
      simp [F, hp, w_zero]
    simp [this]
  rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn],
    Finset.tsum_subtype' n.divisorsAntidiagonal (fun p => F b α p)]
  have hΛ : (Λ n : ℝ) = ∑ p ∈ n.divisorsAntidiagonal, ((μ p.1 : ℤ) : ℝ) * Real.log p.2 := by
    rw [← ArithmeticFunction.moebius_mul_log_eq_vonMangoldt, ArithmeticFunction.mul_apply]
    simp [ArithmeticFunction.intCoe_apply, ArithmeticFunction.log_apply]
  have hw : ∀ p ∈ n.divisorsAntidiagonal, F b α p = (((μ p.1 : ℤ) : ℝ) * Real.log p.2 : ℝ) * w b α n := by
    intro p hp
    have := (Nat.mem_divisorsAntidiagonal.mp hp).1
    simp only [F, this]; push_cast; ring
  rw [Finset.sum_congr rfl hw, ← Finset.sum_mul, hΛ]
  push_cast; rfl

/-- **`S_b(α) = Σ_m μ(m) Σ_k log k · w(mk)`.** -/
theorem primeSumSym_eq_moebius_double {b : ℝ} (hb : 0 < b) (α : ℝ) :
    primeSumSym b α = ∑' m : ℕ, ∑' k : ℕ, F b α (m, k) := by
  have hF := (summable_F hb α).hasSum
  have hfib := hF.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  simp only [fibre_sum] at hfib
  rw [FleetPrimeOnlyRH.primeSumSym_eq hb, ← (summable_F hb α).tsum_prod, ← hfib.tsum_eq]
  congr 1; funext n; unfold term w; ring

/-- Inner sum regrouped as `m^{-1/2} · I_b(α, log m)` for `m ≥ 1`. -/
lemma inner_eq {b α : ℝ} {m : ℕ} (hm : 0 < m) :
    ∑' k : ℕ, (Real.log k : ℂ) * w b α (m * k) = (m : ℂ) ^ (-(1 / 2) : ℂ) * Ismooth b α (Real.log m) := by
  unfold Ismooth
  rw [← tsum_mul_left]
  congr 1; funext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  unfold w
  have hlog : Real.log ((m * k : ℕ) : ℝ) = Real.log k + Real.log m := by
    push_cast; rw [Real.log_mul (by positivity) (by positivity)]; ring
  rw [hlog]
  push_cast
  rw [Complex.natCast_mul_natCast_cpow]
  ring

/-- **`Λ = μ ∗ log` with the Gaussian weight kept at `log(mk)`:**
`S_b(α) = Σ_{m} μ(m) m^{-1/2} I_b(α, log m)`, `I_b` a smooth sum over all integers. -/
theorem primeSumSym_eq_moebius_smooth {b : ℝ} (hb : 0 < b) (α : ℝ) :
    primeSumSym b α = ∑' m : ℕ, ((μ m : ℤ) : ℂ) * (m : ℂ) ^ (-(1 / 2) : ℂ) * Ismooth b α (Real.log m) := by
  rw [primeSumSym_eq_moebius_double hb α]
  congr 1; funext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [F]
  have e : ∑' k : ℕ, F b α (m, k) = ((μ m : ℤ) : ℂ) * ∑' k : ℕ, (Real.log k : ℂ) * w b α (m * k) := by
    rw [← tsum_mul_left]; congr 1; funext k; simp only [F]; ring
  rw [e, inner_eq hm]; ring

end FleetMoebiusSmoothDecomposition
