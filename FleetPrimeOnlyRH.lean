import FleetPrimeSideConsequences
import Mathlib

/-!
# Primes only: the proper prime powers cost `O(b^{-1/2})`

`primeSumSym b α = Σ Λ(n) n^{-1/2} (g(log n) + g(-log n))` runs over all prime powers. This file
splits off the proper prime powers `p^k`, `k ≥ 2`, and shows they contribute at most `√(π/b)·K`
for all `0 < b ≤ 1`, with `K` independent of `α`. Hence the RH criterion holds with the sum over
primes `p` alone:

  `RH_iff_primeOnly_bound` : RH ↔ ∀ α, ∃ C', ∀ b ∈ (0,1], ‖P_b(α) − Σ_p log p · p^{-1/2}(g(log p)+g(-log p))‖ ≤ √(π/b) C'.

The `k = 2` part is not `O(1)`: `Σ_p log p / p` diverges. With the Gaussian weight it is
`O(b^{-1/2})`; the proof uses only `θ(n) ≤ n log 4` (from `primorial_le_4_pow`), Abel summation and
`Σ_{m≥1} m^{-1-ε} ≤ 1 + 1/ε`, with `ε = √b`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Finset
open scoped Real ArithmeticFunction
open GaussianTest FleetPrimePoleBoundRH FleetPrimeSideConsequences

namespace FleetPrimeOnlyRH

/-! ## Elementary prime-counting inputs -/

/-- `log p` on primes, `0` elsewhere. -/
def thetaW (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

lemma thetaW_nonneg (n : ℕ) : 0 ≤ thetaW n := by
  unfold thetaW; split_ifs
  · exact Real.log_natCast_nonneg n
  · exact le_rfl

lemma thetaW_le_vonMangoldt (n : ℕ) : thetaW n ≤ Λ n := by
  unfold thetaW; split_ifs with h
  · rw [ArithmeticFunction.vonMangoldt_apply_prime h]
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- Chebyshev: `θ(n) ≤ n log 4`. -/
lemma sum_thetaW_le (n : ℕ) : ∑ m ∈ range n, thetaW (m + 1) ≤ Real.log 4 * n := by
  have h1 : ∑ m ∈ range n, thetaW (m + 1) = ∑ m ∈ range (n + 1), thetaW m := by
    rw [Finset.sum_range_succ']; simp [thetaW, Nat.not_prime_zero]
  have h2 : ∑ m ∈ range (n + 1), thetaW m
      = ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p := by
    rw [Finset.sum_filter]; rfl
  have h3 : ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p = Real.log (primorial n : ℝ) := by
    unfold primorial
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  have h4 : Real.log (primorial n : ℝ) ≤ Real.log ((4 : ℝ) ^ n) := by
    apply Real.log_le_log
    · exact_mod_cast primorial_pos n
    · exact_mod_cast primorial_le_four_pow n
  rw [h1, h2, h3]
  refine h4.trans (le_of_eq ?_)
  rw [Real.log_pow]; ring

/-- Abel summation: partial sums of `a` at most `c·n`, `w` antitone and nonnegative. -/
lemma abel_le {a w : ℕ → ℝ} {c : ℝ} (hA : ∀ n, ∑ m ∈ range n, a m ≤ c * n)
    (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n) (N : ℕ) :
    ∑ m ∈ range N, a m * w m ≤ c * ∑ m ∈ range N, w m := by
  have key : ∀ N : ℕ, ∑ m ∈ range N, a m * w m + (c * N - ∑ m ∈ range N, a m) * w N
      ≤ c * ∑ m ∈ range N, w m := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      have hA1 := hA (N + 1)
      rw [Finset.sum_range_succ] at hA1
      have hmono : w (N + 1) ≤ w N := hw (Nat.le_succ N)
      push_cast at hA1 ⊢
      nlinarith [mul_le_mul_of_nonneg_left hmono (by linarith : (0:ℝ) ≤ c * (N + 1) - (∑ m ∈ range N, a m + a N))]
  have h := key N
  have hpos : 0 ≤ (c * N - ∑ m ∈ range N, a m) * w N :=
    mul_nonneg (by linarith [hA N]) (hw0 N)
  linarith

/-- `Σ_{m<N} (m+1)^{-1-ε} ≤ 1 + 1/ε`, written with `exp`/`log`. -/
lemma sum_pow_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∑ m ∈ range N, Real.exp (-(1 + ε) * Real.log ((m : ℝ) + 1)) ≤ 1 + 1 / ε := by
  have step : ∀ j : ℕ, Real.exp (-(1 + ε) * Real.log ((j : ℝ) + 2))
      ≤ (1 / ε) * (Real.exp (-ε * Real.log ((j : ℝ) + 1)) - Real.exp (-ε * Real.log ((j : ℝ) + 2))) := by
    intro j
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hj2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    set L1 := Real.log ((j : ℝ) + 1)
    set L2 := Real.log ((j : ℝ) + 2)
    have hd : 1 / ((j : ℝ) + 2) ≤ L2 - L1 := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < ((j : ℝ) + 1) / ((j : ℝ) + 2))
      rw [Real.log_div hj1.ne' hj2.ne'] at this
      have e : ((j : ℝ) + 1) / ((j : ℝ) + 2) - 1 = -(1 / ((j : ℝ) + 2)) := by field_simp; ring
      linarith
    have hE : Real.exp (-ε * L1) ≥ Real.exp (-ε * L2) * (1 + ε * (L2 - L1)) := by
      have : Real.exp (-ε * L1) = Real.exp (-ε * L2) * Real.exp (ε * (L2 - L1)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have := Real.add_one_le_exp (ε * (L2 - L1)); linarith
    have hinv : Real.exp (-L2) = 1 / ((j : ℝ) + 2) := by
      rw [Real.exp_neg, Real.exp_log hj2, one_div]
    have hsplit : Real.exp (-(1 + ε) * L2) = Real.exp (-ε * L2) * (1 / ((j : ℝ) + 2)) := by
      rw [← hinv, ← Real.exp_add]; ring_nf
    rw [hsplit]
    have hpos := Real.exp_pos (-ε * L2)
    have h3 : Real.exp (-ε * L2) * (1 / ((j : ℝ) + 2)) * ε
        ≤ Real.exp (-ε * L1) - Real.exp (-ε * L2) := by
      nlinarith [mul_le_mul_of_nonneg_left hd hpos.le]
    calc Real.exp (-ε * L2) * (1 / ((j : ℝ) + 2))
        = (1 / ε) * (Real.exp (-ε * L2) * (1 / ((j : ℝ) + 2)) * ε) := by field_simp
      _ ≤ (1 / ε) * (Real.exp (-ε * L1) - Real.exp (-ε * L2)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  cases N with
  | zero => simp; positivity
  | succ N =>
    rw [Finset.sum_range_succ']
    have h0 : Real.exp (-(1 + ε) * Real.log (((0 : ℕ) : ℝ) + 1)) = 1 := by simp
    rw [h0]
    have hs : ∑ j ∈ range N, Real.exp (-(1 + ε) * Real.log (((j + 1 : ℕ) : ℝ) + 1))
        ≤ ∑ j ∈ range N, (1 / ε) * (Real.exp (-ε * Real.log ((j : ℝ) + 1))
            - Real.exp (-ε * Real.log ((j : ℝ) + 2))) := by
      apply Finset.sum_le_sum; intro j _
      have := step j; push_cast; ring_nf; ring_nf at this; linarith
    rw [← Finset.mul_sum] at hs
    have ht := Finset.sum_range_sub' (fun j : ℕ => Real.exp (-ε * Real.log ((j : ℝ) + 1))) N
    have e2 : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) + 1 = (i : ℝ) + 2 := by intro i; push_cast; ring
    simp only [e2, Nat.cast_zero, zero_add, Real.log_one, mul_zero, Real.exp_zero] at ht
    rw [ht] at hs
    have hpos := Real.exp_pos (-ε * Real.log ((N : ℝ) + 1))
    have h1e : 0 ≤ 1 / ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 - Real.exp (-ε * Real.log ((N : ℝ) + 1)) ≤ 1) h1e]

/-! ## The Gaussian-weighted sum over primes -/

lemma exp_quad_le {b L : ℝ} (hb : 0 < b) :
    Real.exp (-L - 4 * b * L ^ 2) ≤ Real.exp (1 / 16) * Real.exp (-(1 + Real.sqrt b) * L) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := Real.sq_sqrt hb.le
  nlinarith [sq_nonneg (2 * Real.sqrt b * L - 1 / 4)]

/-- `Σ_p log p · p^{-1} e^{-4b log² p} ≤ e^{1/16} log 4 (1 + 1/√b)`. -/
lemma primes_weighted {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℕ => thetaW n * Real.exp (-Real.log n - 4 * b * Real.log n ^ 2)) ∧
    ∑' n : ℕ, thetaW n * Real.exp (-Real.log n - 4 * b * Real.log n ^ 2)
      ≤ Real.exp (1 / 16) * Real.log 4 * (1 + 1 / Real.sqrt b) := by
  set f : ℕ → ℝ := fun n => thetaW n * Real.exp (-Real.log n - 4 * b * Real.log n ^ 2)
  have hf0 : ∀ n, 0 ≤ f n := fun n => mul_nonneg (thetaW_nonneg n) (Real.exp_pos _).le
  have hsum : Summable f := by
    refine Summable.of_nonneg_of_le hf0 (fun n => ?_)
      (GaussianTraceFormula.summable_primeBound (by positivity : 0 < 4 * b))
    unfold GaussianTraceFormula.primeBound
    apply mul_le_mul (thetaW_le_vonMangoldt n) _ (Real.exp_pos _).le ArithmeticFunction.vonMangoldt_nonneg
    apply Real.exp_le_exp.mpr
    have := Real.log_natCast_nonneg n
    nlinarith
  refine ⟨hsum, Real.tsum_le_of_sum_range_le hf0 (fun N => ?_)⟩
  set ε := Real.sqrt b
  have hε : 0 < ε := Real.sqrt_pos.mpr hb
  set w : ℕ → ℝ := fun m => Real.exp (-(1 + ε) * Real.log ((m : ℝ) + 1))
  have hw : Antitone w := by
    intro m n hmn
    apply Real.exp_le_exp.mpr
    have : Real.log ((m : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    nlinarith
  have hw0 : ∀ m, 0 ≤ w m := fun m => (Real.exp_pos _).le
  have hab := abel_le (a := fun m => thetaW (m + 1)) (c := Real.log 4) sum_thetaW_le hw hw0 N
  have hsp := sum_pow_le hε N
  have h1 : ∑ n ∈ range N, f n ≤ ∑ m ∈ range N, f (m + 1) := by
    have : ∑ n ∈ range N, f n ≤ ∑ n ∈ range (N + 1), f n := by
      rw [Finset.sum_range_succ]; linarith [hf0 N]
    refine this.trans (le_of_eq ?_)
    rw [Finset.sum_range_succ']
    simp [f, thetaW, Nat.not_prime_zero]
  have h2 : ∀ m : ℕ, f (m + 1) ≤ Real.exp (1 / 16) * (thetaW (m + 1) * w m) := by
    intro m
    simp only [f, w]
    have := exp_quad_le (L := Real.log ((m + 1 : ℕ) : ℝ)) hb
    push_cast at this ⊢
    nlinarith [thetaW_nonneg (m + 1), mul_le_mul_of_nonneg_left this (thetaW_nonneg (m + 1))]
  have h3 : ∑ m ∈ range N, f (m + 1) ≤ Real.exp (1 / 16) * ∑ m ∈ range N, thetaW (m + 1) * w m := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun m _ => h2 m)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have he : 0 ≤ Real.exp (1 / 16) := (Real.exp_pos _).le
  calc ∑ n ∈ range N, f n ≤ Real.exp (1 / 16) * ∑ m ∈ range N, thetaW (m + 1) * w m := h1.trans h3
    _ ≤ Real.exp (1 / 16) * (Real.log 4 * ∑ m ∈ range N, w m) := mul_le_mul_of_nonneg_left hab he
    _ ≤ Real.exp (1 / 16) * (Real.log 4 * (1 + 1 / ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsp hl4) he
    _ = _ := by ring

/-! ## The proper prime powers -/

/-- Proper-prime-power weight `Λ(n) − [n prime] log n`. -/
def rW (n : ℕ) : ℝ := Λ n - thetaW n

lemma rW_nonneg (n : ℕ) : 0 ≤ rW n := by unfold rW; linarith [thetaW_le_vonMangoldt n]
lemma rW_le (n : ℕ) : rW n ≤ Λ n := by unfold rW; linarith [thetaW_nonneg n]

/-- Real majorant of `|n^{-1/2}(g(log n) + g(-log n))|`. -/
def vW (b : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(1 / 2) * Real.log n) * (2 * Real.exp (-b * Real.log n ^ 2))

lemma vW_nonneg (b : ℝ) (n : ℕ) : 0 ≤ vW b n := by unfold vW; positivity

lemma vW_le (b : ℝ) (n : ℕ) : vW b n ≤ 2 * Real.exp (-b * Real.log n ^ 2) := by
  unfold vW
  have : Real.exp (-(1 / 2) * Real.log n) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.log_natCast_nonneg n]
  have := Real.exp_pos (-b * Real.log n ^ 2)
  nlinarith

lemma summable_c_vW {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ Λ n) {b : ℝ} (hb : 0 < b) :
    Summable (fun n => |c n| * vW b n) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (vW_nonneg b n)) (fun n => ?_)
    ((GaussianTraceFormula.summable_primeBound hb).mul_left 2)
  unfold GaussianTraceFormula.primeBound
  have := mul_le_mul (hc n) (vW_le b n) (vW_nonneg b n) ArithmeticFunction.vonMangoldt_nonneg
  linarith

lemma vonMangoldt_pow_prime {p : ℕ} (hp : p.Prime) (k : ℕ) : Λ (p ^ (k + 2)) = Real.log p := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- **The proper prime powers cost `O(b^{-1/2})`**, uniformly in nothing but `b ≤ 1`. -/
theorem tsum_rW_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 < b → b ≤ 1 →
    ∑' n : ℕ, rW n * vW b n ≤ Real.sqrt (π / b) * K := by
  set r : ℝ := Real.exp (-(Real.log 2 / 2))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2)
    calc r < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  refine ⟨4 * Real.exp (1 / 16) * Real.log 4 * (1 - r)⁻¹, ?_, fun b hb hb1 => ?_⟩
  · have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    have : 0 < 1 - r := by linarith
    positivity
  classical
  set F : ℕ → ℝ := fun n => rW n * vW b n
  have hF0 : ∀ n, 0 ≤ F n := fun n => mul_nonneg (rW_nonneg n) (vW_nonneg b n)
  have hFs : Summable F := by
    have := summable_c_vW (c := rW) (fun n => by rw [_root_.abs_of_nonneg (rW_nonneg n)]; exact rW_le n) hb
    simpa [F, _root_.abs_of_nonneg (rW_nonneg _)] using this
  set φ : Nat.Primes × ℕ → ℕ := fun x => (x.1 : ℕ) ^ (x.2 + 2)
  have hφ : Function.Injective φ := by
    rintro ⟨p, k⟩ ⟨q, j⟩ h
    have h' : (p : ℕ) ^ ((k + 1) + 1) = (q : ℕ) ^ ((j + 1) + 1) := h
    obtain ⟨hpq, hkj⟩ := Nat.Prime.pow_inj p.2 q.2 h'
    exact Prod.ext (Subtype.ext hpq) (by simp only; omega)
  have hsupp : Function.support F ⊆ Set.range φ := by
    intro n hn
    have hr : rW n ≠ 0 := fun h0 => hn (by simp [F, h0])
    by_cases hpr : n.Prime
    · exact absurd (by simp [rW, thetaW, hpr, ArithmeticFunction.vonMangoldt_apply_prime hpr]) hr
    have hΛ : Λ n ≠ 0 := by
      intro h0; apply hr; simp [rW, thetaW, hpr, h0]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hk1 : k ≠ 1 := by rintro rfl; exact hpr (by simpa using hp)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    exact ⟨(⟨p, hp⟩, j), rfl⟩
  rw [← hφ.tsum_eq hsupp]
  -- the majorant G(p, k) = g p · r^k
  set g : Nat.Primes → ℝ := fun p => 2 * (thetaW p * Real.exp (-Real.log p - 4 * b * Real.log p ^ 2))
  obtain ⟨hfs, hfb⟩ := primes_weighted hb
  have hg0 : 0 ≤ g := fun p => by
    simp only [g]; exact mul_nonneg (by norm_num) (mul_nonneg (thetaW_nonneg _) (Real.exp_pos _).le)
  have hgs : Summable g := (hfs.comp_injective Subtype.val_injective).mul_left 2
  have hhs : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
  have hh0 : 0 ≤ (fun k : ℕ => r ^ k) := fun k => pow_nonneg hr0 k
  have hpt : ∀ x : Nat.Primes × ℕ, F (φ x) ≤ g x.1 * r ^ x.2 := by
    rintro ⟨p, k⟩
    have hp := p.2
    have hL : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    simp only [F, φ, g, vW, thetaW, if_pos hp]
    have hlogpow : Real.log (((p : ℕ) ^ (k + 2) : ℕ) : ℝ) = (k + 2 : ℝ) * Real.log p := by
      push_cast; rw [Real.log_pow]; push_cast; ring
    rw [hlogpow]
    have hrW : rW ((p : ℕ) ^ (k + 2)) ≤ Real.log p := by
      have := rW_le ((p : ℕ) ^ (k + 2)); rwa [vonMangoldt_pow_prime hp] at this
    have hrk : r ^ k = Real.exp (k * (-(Real.log 2 / 2))) := by rw [Real.exp_nat_mul]
    rw [hrk]
    set L := Real.log (p : ℝ)
    have hE : Real.exp (-(1 / 2) * ((k + 2 : ℝ) * L)) * (2 * Real.exp (-b * ((k + 2 : ℝ) * L) ^ 2))
        ≤ 2 * (Real.exp (-L - 4 * b * L ^ 2) * Real.exp (k * (-(Real.log 2 / 2)))) := by
      rw [mul_left_comm, ← Real.exp_add, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hb' : 0 ≤ b * L ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hL hk, mul_nonneg hk hb', mul_nonneg (mul_nonneg hk hk) hb']
    have hrW0 := rW_nonneg ((p : ℕ) ^ (k + 2))
    have hv0 : 0 ≤ Real.exp (-(1 / 2) * ((k + 2 : ℝ) * L)) * (2 * Real.exp (-b * ((k + 2 : ℝ) * L) ^ 2)) := by
      positivity
    have hL0' : 0 ≤ L := le_trans hL0.le hL
    calc rW ((p : ℕ) ^ (k + 2)) * (Real.exp (-(1 / 2) * ((k + 2 : ℝ) * L)) * (2 * Real.exp (-b * ((k + 2 : ℝ) * L) ^ 2)))
        ≤ L * (2 * (Real.exp (-L - 4 * b * L ^ 2) * Real.exp (k * (-(Real.log 2 / 2))))) :=
          mul_le_mul hrW hE hv0 hL0'
      _ = 2 * (L * Real.exp (-L - 4 * b * L ^ 2)) * Real.exp (k * (-(Real.log 2 / 2))) := by ring
  have hGs : Summable (fun x : Nat.Primes × ℕ => g x.1 * r ^ x.2) := hgs.mul_of_nonneg hhs hg0 hh0
  have hle := Summable.tsum_le_tsum hpt (hFs.comp_injective hφ) hGs
  have hprod : ∑' x : Nat.Primes × ℕ, g x.1 * r ^ x.2 = (∑' p, g p) * ∑' k : ℕ, r ^ k := by
    rw [tsum_mul_tsum_of_summable_norm]
    · simpa [Real.norm_eq_abs, _root_.abs_of_nonneg (hg0 _)] using hgs
    · simpa [Real.norm_eq_abs, _root_.abs_of_nonneg (pow_nonneg hr0 _)] using hhs
  have hgp : ∑' p, g p ≤ 2 * (Real.exp (1 / 16) * Real.log 4 * (1 + 1 / Real.sqrt b)) := by
    have := tsum_comp_le_tsum_of_inj hfs (fun n => mul_nonneg (thetaW_nonneg n) (Real.exp_pos _).le)
      Subtype.val_injective (β := Nat.Primes)
    simp only [g]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (this.trans hfb) (by norm_num)
  rw [tsum_geometric_of_lt_one hr0 hr1] at hprod
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have h1b : 1 ≤ 1 / Real.sqrt b := by
    rw [le_div_iff₀ hsb, one_mul]
    calc Real.sqrt b ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hb1
      _ = 1 := Real.sqrt_one
  have hpib : 1 / Real.sqrt b ≤ Real.sqrt (π / b) := by
    rw [Real.sqrt_div Real.pi_pos.le b]
    apply div_le_div_of_nonneg_right _ hsb.le
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt π := Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
  have hinv : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (by linarith)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have he := Real.exp_pos (1 / 16)
  calc ∑' x, F (φ x) ≤ (∑' p, g p) * (1 - r)⁻¹ := hle.trans (le_of_eq hprod)
    _ ≤ 2 * (Real.exp (1 / 16) * Real.log 4 * (1 + 1 / Real.sqrt b)) * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_right hgp hinv
    _ ≤ 2 * (Real.exp (1 / 16) * Real.log 4 * (2 * Real.sqrt (π / b))) * (1 - r)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hinv
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = Real.sqrt (π / b) * (4 * Real.exp (1 / 16) * Real.log 4 * (1 - r)⁻¹) := by ring

/-! ## The criterion over primes only -/

/-- The symmetric term with coefficient `c n`. -/
def term (c : ℕ → ℝ) (b α : ℝ) (n : ℕ) : ℂ :=
  (c n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * (gauss b α (Real.log n) + gauss b α (-Real.log n))

/-- The prime-only sum `Σ_p log p · p^{-1/2} (g(log p) + g(-log p))`. -/
def primeOnlySym (b α : ℝ) : ℂ := ∑' n : ℕ, term thetaW b α n

lemma norm_cpow_neg_half (n : ℕ) :
    ‖(n : ℂ) ^ (-(1 / 2) : ℂ)‖ ≤ Real.exp (-(1 / 2) * Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Complex.zero_cpow (by norm_num)]; simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) by norm_cast,
      Complex.norm_cpow_eq_rpow_re_of_pos hn', Real.rpow_def_of_pos hn']
    apply le_of_eq; congr 1; simp; ring

lemma norm_term_le (c : ℕ → ℝ) (b α : ℝ) (n : ℕ) : ‖term c b α n‖ ≤ |c n| * vW b n := by
  unfold term vW
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hg : ‖gauss b α (Real.log n) + gauss b α (-Real.log n)‖ ≤ 2 * Real.exp (-b * Real.log n ^ 2) := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_gauss, norm_gauss, neg_sq]; ring
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (norm_cpow_neg_half n) hg (norm_nonneg _)
    (Real.exp_pos _).le) (abs_nonneg _)

lemma summable_term {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ Λ n) {b : ℝ} (hb : 0 < b) (α : ℝ) :
    Summable (term c b α) :=
  Summable.of_norm_bounded (summable_c_vW hc hb) (norm_term_le c b α)

lemma abs_vonMangoldt_le (n : ℕ) : |Λ n| ≤ Λ n := by
  rw [_root_.abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
lemma abs_thetaW_le (n : ℕ) : |thetaW n| ≤ Λ n := by
  rw [_root_.abs_of_nonneg (thetaW_nonneg n)]; exact thetaW_le_vonMangoldt n
lemma abs_rW_le (n : ℕ) : |rW n| ≤ Λ n := by
  rw [_root_.abs_of_nonneg (rW_nonneg n)]; exact rW_le n

lemma primeSumSym_eq {b : ℝ} (hb : 0 < b) (α : ℝ) :
    primeSumSym b α = ∑' n : ℕ, term (fun n => Λ n) b α n := by
  have hpiece : ∀ sg : ℝ, sg = 1 ∨ sg = -1 → Summable (fun n : ℕ =>
      (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * gauss b α (sg * Real.log n)) := by
    intro sg hsg
    refine Summable.of_norm_bounded (GaussianTraceFormula.summable_primeBound hb) (fun n => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      _root_.abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, norm_gauss]
    unfold GaussianTraceFormula.primeBound
    have hsg2 : (sg * Real.log n) ^ 2 = Real.log n ^ 2 := by
      rcases hsg with rfl | rfl <;> ring
    rw [hsg2]
    have hc1 := GaussianTraceFormula.norm_natCast_cpow_neg_half_le n
    have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have he := Real.exp_pos (-b * Real.log n ^ 2)
    have hA := mul_le_mul_of_nonneg_left hc1 h0
    nlinarith [mul_le_mul_of_nonneg_right hA he.le]
  have h1 := hpiece 1 (Or.inl rfl)
  have h2 := hpiece (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at h1 h2
  unfold primeSumSym GammaExplicitFormula.primeSum GammaExplicitFormula.reflect term
  rw [← h1.tsum_add h2]
  congr 1; funext n; ring

/-- **Dropping the proper prime powers costs `O(b^{-1/2})`**, uniformly in `α`. -/
theorem norm_primeSumSym_sub_primeOnlySym_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ α b : ℝ, 0 < b → b ≤ 1 →
    ‖primeSumSym b α - primeOnlySym b α‖ ≤ Real.sqrt (π / b) * K := by
  obtain ⟨K, hK, hR⟩ := tsum_rW_le
  refine ⟨K, hK, fun α b hb hb1 => ?_⟩
  have hsΛ := summable_term abs_vonMangoldt_le hb α
  have hsθ := summable_term abs_thetaW_le hb α
  have hsr := summable_term abs_rW_le hb α
  have e : primeSumSym b α - primeOnlySym b α = ∑' n : ℕ, term rW b α n := by
    rw [primeSumSym_eq hb, primeOnlySym, ← hsΛ.tsum_sub hsθ]
    congr 1; funext n; unfold term rW; push_cast; ring
  rw [e]
  have hnorm : Summable (fun n => ‖term rW b α n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_term_le rW b α) (summable_c_vW abs_rW_le hb)
  calc ‖∑' n : ℕ, term rW b α n‖ ≤ ∑' n : ℕ, ‖term rW b α n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, rW n * vW b n := by
        refine Summable.tsum_le_tsum (fun n => ?_) hnorm ?_
        · have := norm_term_le rW b α n; rwa [_root_.abs_of_nonneg (rW_nonneg n)] at this
        · simpa [_root_.abs_of_nonneg (rW_nonneg _)] using summable_c_vW abs_rW_le hb
    _ ≤ _ := hR b hb hb1

/-- **RH over primes only.** -/
theorem RH_iff_primeOnly_bound :
    RiemannHypothesis ↔ ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖poleTerm b α - primeOnlySym b α‖ ≤ Real.sqrt (π / b) * C' := by
  obtain ⟨K, hK, hD⟩ := norm_primeSumSym_sub_primeOnlySym_le
  rw [RH_iff_pole_prime_bound]
  constructor
  · intro h α
    obtain ⟨C', hC'⟩ := h α
    refine ⟨C' + K, fun b hb hb1 => ?_⟩
    have e : poleTerm b α - primeOnlySym b α
        = poleMinusPrimes b α + (primeSumSym b α - primeOnlySym b α) := by
      rw [poleMinusPrimes_eq]; ring
    rw [e, mul_add]
    exact (norm_add_le _ _).trans (add_le_add (hC' b hb hb1) (hD α b hb hb1))
  · intro h α
    obtain ⟨C', hC'⟩ := h α
    refine ⟨C' + K, fun b hb hb1 => ?_⟩
    have e : poleMinusPrimes b α
        = (poleTerm b α - primeOnlySym b α) - (primeSumSym b α - primeOnlySym b α) := by
      rw [poleMinusPrimes_eq]; ring
    rw [e, mul_add]
    exact (norm_sub_le _ _).trans (add_le_add (hC' b hb hb1) (hD α b hb hb1))

/-- **For `|α| ≥ 1/2` only the sum over primes remains.** -/
theorem pole_prime_bound_iff_primeOnly_bound {α : ℝ} (hα : (1 / 2 : ℝ) ≤ |α|) :
    (∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 → ‖poleMinusPrimes b α‖ ≤ Real.sqrt (π / b) * C') ↔
    (∃ C'' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 → ‖primeOnlySym b α‖ ≤ Real.sqrt (π / b) * C'') := by
  obtain ⟨K, hK, hD⟩ := norm_primeSumSym_sub_primeOnlySym_le
  rw [poleMinusPrimes_bound_iff_primeSumSym_bound hα]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + K, fun b hb hb1 => ?_⟩
    have e : primeOnlySym b α = primeSumSym b α - (primeSumSym b α - primeOnlySym b α) := by ring
    rw [e, mul_add]
    exact (norm_sub_le _ _).trans (add_le_add (hC b hb hb1) (hD α b hb hb1))
  · rintro ⟨C, hC⟩
    refine ⟨C + K, fun b hb hb1 => ?_⟩
    have e : primeSumSym b α = primeOnlySym b α + (primeSumSym b α - primeOnlySym b α) := by ring
    rw [e, mul_add]
    exact (norm_add_le _ _).trans (add_le_add (hC b hb hb1) (hD α b hb hb1))

/-! ## With the low heights verified -/

/-- With zeros verified up to `H ≥ 3/2`, RH needs only the two-sided prime-power sum, at `|α| ≥ 1/2`. -/
theorem RH_iff_primeSumSym_bound_of_verified {H : ℝ} (hH : 3 / 2 ≤ H) (hV : VerifiedTo H) :
    RiemannHypothesis ↔ ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C'' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖primeSumSym b α‖ ≤ Real.sqrt (π / b) * C'' := by
  rw [RH_iff_pole_prime_bound]
  constructor
  · intro h α hα
    exact (poleMinusPrimes_bound_iff_primeSumSym_bound hα).mp (h α)
  · intro h α
    by_cases hα : 1 / 2 ≤ |α|
    · exact (poleMinusPrimes_bound_iff_primeSumSym_bound hα).mpr (h α hα)
    · push_neg at hα
      exact pole_prime_bound_of_verified hV (by linarith)

/-- The same over primes only. -/
theorem RH_iff_primeOnlySym_bound_of_verified {H : ℝ} (hH : 3 / 2 ≤ H) (hV : VerifiedTo H) :
    RiemannHypothesis ↔ ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C'' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖primeOnlySym b α‖ ≤ Real.sqrt (π / b) * C'' := by
  rw [RH_iff_pole_prime_bound]
  constructor
  · intro h α hα
    exact (pole_prime_bound_iff_primeOnly_bound hα).mp (h α)
  · intro h α
    by_cases hα : 1 / 2 ≤ |α|
    · exact (pole_prime_bound_iff_primeOnly_bound hα).mpr (h α hα)
    · push_neg at hα
      exact pole_prime_bound_of_verified hV (by linarith)

end FleetPrimeOnlyRH
