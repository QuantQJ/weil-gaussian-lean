import FleetDivisorCertificate

/-!
# The multiplicative freedom in divisor-certificate multipliers

Multipliers `u` for `FleetDivisorCertificate` are judged only through their coverage at prime powers,
`cov u d = Σ_{n ≤ N, d ∣ n} u n`, and their budget `Σ_{n ≤ N} log n · u n`.

* `budget_eq_of_coverage_eq` : the budget depends only on coverage at prime powers (from `Σ_{d∣n} Λ = log`).
* `coverage_coprime_move` : for coprime `a, b` with `a b ≤ N`, the move `δ_{ab} − δ_a − δ_b` has zero coverage at
  every prime power; with the previous item it also has zero budget (`budget_coprime_move`).
* `coverage_telescope` : `u₀(p^j) = k(p^j) − k(p^{j+1})` (zero off prime powers, `k = 0` beyond `N`) has coverage
  exactly `k` at every prime power `≤ N`.
* `eq_of_coverage_eq` : two multipliers with the same prime-power coverage that agree at every non-prime-power
  `n ≤ N` agree everywhere on `[1, N]`. So an exact-coverage multiplier is determined by its composite coordinates,
  which are free.
-/

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction

namespace FleetMultiplierFreedom
open FleetDivisorCertificate

/-- Coverage of `u` at `d`. -/
def cov (N : ℕ) (u : ℕ → ℝ) (d : ℕ) : ℝ := ∑ n ∈ mult N d, u n

lemma mem_mult {N d n : ℕ} : n ∈ mult N d ↔ 1 ≤ n ∧ n ≤ N ∧ d ∣ n := by
  simp [mult, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- The budget is a function of the prime-power coverage. -/
theorem budget_eq_of_coverage_eq (N : ℕ) (u u' : ℕ → ℝ)
    (h : ∀ d ∈ Icc 1 N, IsPrimePow d → cov N u d = cov N u' d) :
    ∑ n ∈ Icc 1 N, Real.log n * u n = ∑ n ∈ Icc 1 N, Real.log n * u' n := by
  have h1 := swap N u
  have h2 := swap N u'
  simp only [smul_eq_mul] at h1 h2
  rw [← h1, ← h2]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  by_cases hp : IsPrimePow d
  · have := h d hd hp; simp only [cov] at this; rw [this]
  · rw [vonMangoldt_eq_zero_iff.mpr hp, zero_mul, zero_mul]

/-- The coprime move `δ_{ab} − δ_a − δ_b`. -/
def z (a b n : ℕ) : ℝ :=
  (if n = a * b then 1 else 0) - (if n = a then 1 else 0) - (if n = b then 1 else 0)

lemma cov_single (N d c : ℕ) :
    cov N (fun n => if n = c then (1:ℝ) else 0) d = if c ∈ mult N d then 1 else 0 := by
  simp only [cov]; exact Finset.sum_ite_eq' _ _ _

theorem coverage_coprime_move {N a b d : ℕ} (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hN : a * b ≤ N) (hd : IsPrimePow d) : cov N (z a b) d = 0 := by
  have e : cov N (z a b) d = cov N (fun n => if n = a * b then (1:ℝ) else 0) d
      - cov N (fun n => if n = a then (1:ℝ) else 0) d - cov N (fun n => if n = b then (1:ℝ) else 0) d := by
    simp only [cov, z, Finset.sum_sub_distrib]
  rw [e, cov_single, cov_single, cov_single]
  have hab1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
  have hab2 : b ≤ a * b := Nat.le_mul_of_pos_left b ha
  have hm1 : a * b ∈ mult N d ↔ d ∣ a * b := by rw [mem_mult]; constructor <;> intro h <;> [exact h.2.2; exact ⟨by nlinarith, hN, h⟩]
  have hm2 : a ∈ mult N d ↔ d ∣ a := by rw [mem_mult]; constructor <;> intro h <;> [exact h.2.2; exact ⟨ha, by omega, h⟩]
  have hm3 : b ∈ mult N d ↔ d ∣ b := by rw [mem_mult]; constructor <;> intro h <;> [exact h.2.2; exact ⟨hb, by omega, h⟩]
  have hor := hab.isPrimePow_dvd_mul hd
  have hnot : ¬ (d ∣ a ∧ d ∣ b) := by
    rintro ⟨h1, h2⟩
    have : d ∣ Nat.gcd a b := Nat.dvd_gcd h1 h2
    rw [hab] at this
    exact hd.ne_one (Nat.dvd_one.mp this)
  by_cases h1 : d ∣ a <;> by_cases h2 : d ∣ b
  · exact absurd ⟨h1, h2⟩ hnot
  · have : d ∣ a * b := hor.mpr (Or.inl h1)
    simp [hm1.mpr this, hm2.mpr h1, show a * b ∈ mult N d from hm1.mpr this, show a ∈ mult N d from hm2.mpr h1,
      show b ∉ mult N d from fun h => h2 (hm3.mp h)]
  · have : d ∣ a * b := hor.mpr (Or.inr h2)
    simp [show a * b ∈ mult N d from hm1.mpr this, show a ∉ mult N d from fun h => h1 (hm2.mp h),
      show b ∈ mult N d from hm3.mpr h2]
  · have : ¬ d ∣ a * b := fun h => (hor.mp h).elim h1 h2
    simp [show a * b ∉ mult N d from fun h => this (hm1.mp h), show a ∉ mult N d from fun h => h1 (hm2.mp h),
      show b ∉ mult N d from fun h => h2 (hm3.mp h)]

/-- A coprime move changes neither coverage at prime powers nor the budget. -/
theorem budget_coprime_move {N a b : ℕ} (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) (hN : a * b ≤ N)
    (u : ℕ → ℝ) (θ : ℝ) :
    ∑ n ∈ Icc 1 N, Real.log n * (u n + θ * z a b n) = ∑ n ∈ Icc 1 N, Real.log n * u n := by
  apply budget_eq_of_coverage_eq
  intro d _ hd
  have := coverage_coprime_move hab ha hb hN hd
  simp only [cov] at this ⊢
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, this, mul_zero, add_zero]

/-- A prime power `n` divisible by `p^a` (`p` prime, `a ≥ 1`) is `p^j` with `j ≥ a`. -/
lemma primePow_of_dvd {p a n : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hn : IsPrimePow n) (hdvd : p ^ a ∣ n) :
    ∃ j, a ≤ j ∧ n = p ^ j := by
  obtain ⟨q, j, hq, hj, rfl⟩ := (isPrimePow_nat_iff n).1 hn
  have hpq : p ∣ q := hp.dvd_of_dvd_pow ((dvd_pow_self p (by omega)).trans hdvd)
  have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  subst this
  exact ⟨j, (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd, rfl⟩

/-- Prime-power multiples of `p^a` are `p^a` itself and the prime-power multiples of `p^{a+1}`. -/
lemma filter_mult_succ {N p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hN : p ^ a ≤ N) :
    (mult N (p ^ a)).filter IsPrimePow = insert (p ^ a) ((mult N (p ^ (a+1))).filter IsPrimePow) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_insert, mem_mult]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    obtain ⟨j, hj, rfl⟩ := primePow_of_dvd hp ha h4 h3
    rcases Nat.eq_or_lt_of_le hj with h | h
    · left; rw [h]
    · right; exact ⟨⟨h1, h2, Nat.pow_dvd_pow p h⟩, h4⟩
  · rintro (rfl | ⟨⟨h1, h2, h3⟩, h4⟩)
    · exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero), hN, dvd_rfl⟩,
        hp.isPrimePow.pow (by omega)⟩
    · exact ⟨⟨h1, h2, (Nat.pow_dvd_pow p (Nat.le_succ a)).trans h3⟩, h4⟩

/-- Coverage of a multiplier supported on prime powers only sees prime powers. -/
lemma cov_eq_filter (N : ℕ) (w : ℕ → ℝ) (hw : ∀ n, ¬ IsPrimePow n → w n = 0) (d : ℕ) :
    cov N w d = ∑ n ∈ (mult N d).filter IsPrimePow, w n := by
  simp only [cov]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  split_ifs with h
  · rfl
  · exact hw n h

/-- One-step recursion for a prime-power-supported multiplier. -/
lemma cov_step (N : ℕ) (w : ℕ → ℝ) (hw : ∀ n, ¬ IsPrimePow n → w n = 0) {p a : ℕ} (hp : p.Prime)
    (ha : 1 ≤ a) (hN : p ^ a ≤ N) :
    cov N w (p ^ a) = w (p ^ a) + cov N w (p ^ (a+1)) := by
  rw [cov_eq_filter N w hw, cov_eq_filter N w hw, filter_mult_succ hp ha hN, Finset.sum_insert]
  intro hmem
  rw [Finset.mem_filter, mem_mult] at hmem
  have h1 := Nat.le_of_dvd (pow_pos hp.pos a) hmem.1.2.2
  have h2 : p ^ a < p ^ (a+1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self a)
  omega

lemma cov_beyond (N : ℕ) (w : ℕ → ℝ) {d : ℕ} (hd : N < d) : cov N w d = 0 := by
  simp only [cov]
  apply Finset.sum_eq_zero
  intro n hn
  rw [mem_mult] at hn
  exact absurd (Nat.le_of_dvd (by omega) hn.2.2) (by omega)

/-- The telescoping multiplier. -/
def u0 (k : ℕ → ℝ) (n : ℕ) : ℝ := if IsPrimePow n then k n - k (n * n.minFac) else 0

/-- **Telescoping**: `u₀` has coverage exactly `k` at every prime power `≤ N`, when `k = 0` beyond `N`. -/
theorem coverage_telescope (N : ℕ) (k : ℕ → ℝ) (hk : ∀ n, N < n → k n = 0)
    {d : ℕ} (hd : IsPrimePow d) (hdN : d ≤ N) : cov N (u0 k) d = k d := by
  obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff d).1 hd
  have hw : ∀ n, ¬ IsPrimePow n → u0 k n = 0 := fun n h => by simp [u0, h]
  -- induct on N - p^a
  induction' h : N - p ^ a using Nat.strong_induction_on with m ih generalizing a
  rw [cov_step N _ hw hp ha hdN]
  have hu : u0 k (p ^ a) = k (p ^ a) - k (p ^ (a+1)) := by
    have h0 : a ≠ 0 := by omega
    rw [u0, if_pos hd, Nat.Prime.pow_minFac hp h0, pow_succ]
  rw [hu]
  by_cases hnext : p ^ (a+1) ≤ N
  · have hlt : p ^ a < p ^ (a+1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self a)
    rw [ih (N - p ^ (a+1)) (by omega) (a+1) (by omega) (hp.isPrimePow.pow (by omega)) hnext rfl]
    ring
  · push_neg at hnext
    rw [cov_beyond N _ hnext, hk _ hnext]; ring

/-- **Uniqueness**: equal prime-power coverage plus equal values at every non-prime-power `n ≤ N`
force equality on `[1, N]`. -/
theorem eq_of_coverage_eq (N : ℕ) (u u' : ℕ → ℝ)
    (hcov : ∀ d, IsPrimePow d → d ≤ N → cov N u d = cov N u' d)
    (hcomp : ∀ n ∈ Icc 1 N, ¬ IsPrimePow n → u n = u' n) :
    ∀ n ∈ Icc 1 N, u n = u' n := by
  -- the difference, cut to [1, N], is prime-power supported with zero coverage
  set w : ℕ → ℝ := fun n => if n ∈ Icc 1 N then u n - u' n else 0 with hwdef
  have hw : ∀ n, ¬ IsPrimePow n → w n = 0 := by
    intro n hn; simp only [hwdef]; split_ifs with h
    · rw [hcomp n h hn, sub_self]
    · rfl
  have hcw : ∀ d, IsPrimePow d → d ≤ N → cov N w d = 0 := by
    intro d hd hdN
    have : cov N w d = cov N u d - cov N u' d := by
      simp only [cov, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have : n ∈ Icc 1 N := by rw [mem_mult] at hn; exact Finset.mem_Icc.mpr ⟨hn.1, hn.2.1⟩
      simp only [hwdef, if_pos this]
    rw [this, hcov d hd hdN, sub_self]
  intro n hn
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
    have hN : p ^ a ≤ N := (Finset.mem_Icc.mp hn).2
    have step := cov_step N w hw hp ha hN
    have hnext : cov N w (p ^ (a+1)) = 0 := by
      by_cases h : p ^ (a+1) ≤ N
      · exact hcw _ (hp.isPrimePow.pow (by omega)) h
      · push_neg at h; exact cov_beyond N w h
    rw [hcw _ hpp hN, hnext, add_zero] at step
    have : w (p ^ a) = u (p ^ a) - u' (p ^ a) := by simp only [hwdef, if_pos hn]
    linarith
  · exact hcomp n hn hpp

end FleetMultiplierFreedom
