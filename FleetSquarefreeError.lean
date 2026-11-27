import FleetLandauTransfer
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# The squarefree counting error from a Möbius partial-sum bound

`Q(x) = #{n ≤ x : n squarefree}`, `E(x) = Q(x) − 6x/π²`.

* `sqfCount_eq` : `Q(N) = Σ_{d ≤ N} μ(d) ⌊N/d²⌋` (from `Σ_{d² ∣ n} μ(d) = [n squarefree]`).
* `hasSum_moebius_div_sq` : `Σ μ(n)/n² = 6/π²` (Mathlib's `L(ζ)·L(μ) = 1` at `s = 2` and `ζ(2) = π²/6`).
* `main_bound` : the hyperbola split at `Y`: `|E(N)| ≤ Y + K·N·Y^{α−2}` whenever `|Σ_{n≤y} μ(n)| ≤ C y^α`.
* `squarefreeError_of_moebius` : `FleetHeadContour.MoebiusSumBound θ` (`0 ≤ θ ≤ 1`) ⇒
  `|E(x)| ≤ C_ε x^{1/(3−θ)+ε}` for every `ε > 0`, `x ≥ 1` (take `Y = ⌊x^{1/(3−θ−ε')}⌋`).
* `squarefreeError_of_quasiRH` : `QuasiRHWiring.QuasiRH` (carried as a hypothesis) ⇒ exponent `8/17 + ε`
  (`θ = 7/8` from `FleetHeadContour.landauTransfer (3/8)` and `stripBound_of_quasiRH`).
* `squarefreeError_of_RH` : RH ⇒ exponent `2/5 + ε` (`θ = 1/2`, `landauTransfer 0`).

`sqfCount` is the same definition as `Erdos969.squarefreeCounting` in google-deepmind/formal-conjectures
(`FormalConjectures/ErdosProblems/969.lean`); no code from that file is used here.
-/

noncomputable section
open Finset
open scoped ArithmeticFunction.Moebius

namespace FleetSquarefreeError

/-- `Q(N) = #{1 ≤ n ≤ N : n squarefree}`. -/
def sqfCount (N : ℕ) : ℕ := ((Finset.Icc 1 N).filter Squarefree).card

/-- `Q(x) = Q(⌊x⌋)` for real `x`. -/
def Q (x : ℝ) : ℕ := sqfCount ⌊x⌋₊

/-! ## 1. `Q(N) = Σ_{d ≤ N} μ(d) ⌊N/d²⌋` -/

lemma sq_dvd_sq_mul_iff {a b d : ℕ} (ha : Squarefree a) : d ^ 2 ∣ b ^ 2 * a ↔ d ∣ b := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos (d.gcd b) with h0 | hg
    · rw [Nat.gcd_eq_zero_iff] at h0
      rw [h0.2]; exact dvd_zero _
    obtain ⟨g, d', b', hg0, hcop, rfl, rfl⟩ := Nat.exists_coprime' hg
    have h1 : d' ^ 2 * g ^ 2 ∣ b' ^ 2 * a * g ^ 2 := by
      have : (d' * g) ^ 2 = d' ^ 2 * g ^ 2 := by ring
      have e : (b' * g) ^ 2 * a = b' ^ 2 * a * g ^ 2 := by ring
      rw [this, e] at h; exact h
    have h2 : d' ^ 2 ∣ b' ^ 2 * a := Nat.dvd_of_mul_dvd_mul_right (by positivity) h1
    have h3 : d' ^ 2 ∣ a := (Nat.Coprime.pow 2 2 hcop).dvd_of_dvd_mul_left h2
    have h4 : IsUnit d' := ha d' (by rw [← sq]; exact h3)
    rw [Nat.isUnit_iff] at h4
    subst h4
    simp
  · intro h
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd h 2) a

lemma sum_moebius_sq_dvd {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ^ 2 ∣ n), (μ d : ℤ) =
      if Squarefree n then 1 else 0 := by
  obtain ⟨b, a, hba, ha⟩ := exists_sq_mul_squarefree n
  have hb0 : b ≠ 0 := by
    rintro rfl; simp at hba; omega
  have hset : (Finset.Icc 1 N).filter (fun d => d ^ 2 ∣ n) = b.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    rw [← hba, sq_dvd_sq_mul_iff ha]
    constructor
    · rintro ⟨-, h⟩; exact ⟨h, hb0⟩
    · rintro ⟨h, -⟩
      have hd : 1 ≤ d := Nat.pos_of_ne_zero (by rintro rfl; simp at h; exact hb0 h)
      refine ⟨⟨hd, ?_⟩, h⟩
      have : d ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) h
      have hb2 : b ≤ b ^ 2 * a := by
        have ha0 : 1 ≤ a := Nat.pos_of_ne_zero ha.ne_zero
        nlinarith [Nat.pos_of_ne_zero hb0]
      omega
  rw [hset]
  have hsum : ∑ d ∈ b.divisors, (μ d : ℤ) = if b = 1 then 1 else 0 := by
    have := congrArg (fun f : ArithmeticFunction ℤ => f b) ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at this
    exact this
  rw [hsum]
  have hiff : b = 1 ↔ Squarefree n := by
    constructor
    · rintro rfl; rw [← hba]; simpa using ha
    · intro hs
      have : IsUnit b := hs b (by rw [← hba]; exact ⟨a, by ring⟩)
      exact Nat.isUnit_iff.mp this
  by_cases h : b = 1
  · simp [h, hiff.mp h]
  · simp [h, mt hiff.mpr h]

theorem sqfCount_eq (N : ℕ) :
    (sqfCount N : ℤ) = ∑ d ∈ Finset.Icc 1 N, (μ d : ℤ) * ((N / d ^ 2 : ℕ) : ℤ) := by
  have h1 : (sqfCount N : ℤ) = ∑ n ∈ Finset.Icc 1 N, (if Squarefree n then (1 : ℤ) else 0) := by
    rw [sqfCount, Finset.card_filter]; push_cast; rfl
  rw [h1]
  have h2 : ∀ n ∈ Finset.Icc 1 N, (if Squarefree n then (1 : ℤ) else 0) =
      ∑ d ∈ Finset.Icc 1 N, if d ^ 2 ∣ n then (μ d : ℤ) else 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [← sum_moebius_sq_dvd hn.1 hn.2, Finset.sum_filter]
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have : Finset.Icc 1 N = Finset.Ioc 0 N := by ext n; simp; omega
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]


/-! ## 2. `Σ μ(n)/n² = 6/π²` -/

/-- `g n = μ(n)/n²` (with `g 0 = 0`). -/
def g (n : ℕ) : ℝ := (μ n : ℝ) / (n : ℝ) ^ 2

theorem hasSum_moebius_div_sq : HasSum g (6 / Real.pi ^ 2) := by
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hsum : LSeriesSummable (fun n => (μ n : ℂ)) 2 :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hval : LSeries (fun n => (μ n : ℂ)) 2 = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at h
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    rw [eq_div_iff (pow_ne_zero 2 hpi)]
    linear_combination 6 * h
  have h : HasSum (LSeries.term (fun n => (μ n : ℂ)) 2) _ := hsum.LSeriesHasSum
  rw [hval] at h
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  funext n
  rw [LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [g]
  · simp only [hn, ↓reduceIte, g]
    push_cast
    rw [show ((2 : ℂ)) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]

/-! ## 3. Partial summation and two power sums -/

/-- `M(n) = Σ_{k ≤ n} μ(k)`, as in `FleetHeadContour.MoebiusSumBound`. -/
def M (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), (μ k : ℝ)

lemma M_succ (n : ℕ) : M (n + 1) = M n + μ (n + 1) := by
  simp only [M]
  rw [Finset.sum_range_succ _ (n + 1)]

lemma sum_range_succ_eq_Ioc (f : ℕ → ℝ) (hf : f 0 = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.Ioc 0 n, f k := by
  induction n with
  | zero => simp [hf]
  | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_Ioc_succ_top (Nat.zero_le n)]

lemma M_eq_Ioc (n : ℕ) : M n = ∑ k ∈ Finset.Ioc 0 n, (μ k : ℝ) :=
  sum_range_succ_eq_Ioc _ (by simp) n

/-- Abel summation for `μ` on `(a, a + L]`. -/
lemma abel (a : ℕ) (f : ℕ → ℝ) (L : ℕ) :
    ∑ i ∈ Finset.range L, (μ (a + 1 + i) : ℝ) * f (a + 1 + i) =
      M (a + L) * f (a + L + 1) - M a * f (a + 1) +
        ∑ i ∈ Finset.range L, M (a + 1 + i) * (f (a + 1 + i) - f (a + 2 + i)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have e1 : a + (L + 1) = a + L + 1 := by ring
    have e2 : a + 1 + L = a + L + 1 := by ring
    have e3 : a + 2 + L = a + L + 1 + 1 := by ring
    rw [e1, e2, e3, M_succ]
    ring

/-- `Σ_{a < n ≤ a+L} n^{α-3} ≤ a^{α-2}/(2-α)`. -/
lemma sum_rpow_tail_le {a : ℕ} (ha : 1 ≤ a) {α : ℝ} (hα : α < 2) (L : ℕ) :
    ∑ i ∈ Finset.range L, ((a + 1 + i : ℕ) : ℝ) ^ (α - 3) ≤ (a : ℝ) ^ (α - 2) / (2 - α) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hanti : AntitoneOn (fun t : ℝ => t ^ (α - 3)) (Set.Icc (a : ℝ) (a + L)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h := hanti.sum_le_integral
  have hnot : (0 : ℝ) ∉ Set.uIcc (a : ℝ) (a + L) := by
    intro h0
    rw [Set.mem_uIcc] at h0
    rcases h0 with h0 | h0 <;> linarith [h0.1, h0.2]
  have hint := integral_rpow (a := (a : ℝ)) (b := a + L) (r := α - 3) (Or.inr ⟨by linarith, hnot⟩)
  rw [hint] at h
  have e : ∀ i ∈ Finset.range L, ((a + 1 + i : ℕ) : ℝ) ^ (α - 3) =
      (fun t : ℝ => t ^ (α - 3)) ((a : ℝ) + ((i + 1 : ℕ) : ℝ)) := by
    intro i _; push_cast; ring_nf
  rw [Finset.sum_congr rfl e]
  refine h.trans ?_
  have h1 : α - 3 + 1 = α - 2 := by ring
  rw [h1]
  have key : ∀ x y : ℝ, (x - y) / (α - 2) = (y - x) / (2 - α) := by
    intro x y; rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  rw [key]
  have h2 : 0 ≤ ((a : ℝ) + L) ^ (α - 2) := Real.rpow_nonneg (by positivity) _
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- `Σ_{1 ≤ m ≤ K} m^{p-1} ≤ K^p/p` for `0 < p ≤ 1` (Bernoulli, telescoped). -/
lemma sum_rpow_head_le {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (K : ℕ) :
    ∑ m ∈ Finset.Ioc 0 K, (m : ℝ) ^ (p - 1) ≤ (K : ℝ) ^ p / p := by
  induction K with
  | zero => simp [Real.zero_rpow hp0.ne']
  | succ K ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le K)]
    push_cast
    have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hs : (-1 : ℝ) ≤ -1 / ((K : ℝ) + 1) := by
      rw [neg_div, neg_le_neg_iff, div_le_one hK1]; linarith
    have hb := rpow_one_add_le_one_add_mul_self hs hp0.le hp1
    have e : 1 + -1 / ((K : ℝ) + 1) = (K : ℝ) / ((K : ℝ) + 1) := by field_simp; ring
    rw [e, Real.div_rpow hK0 hK1.le, div_le_iff₀ (Real.rpow_pos_of_pos hK1 p)] at hb
    rw [Real.rpow_sub_one hK1.ne']
    set X := ((K : ℝ) + 1) ^ p
    have hb' : (K : ℝ) ^ p ≤ X - p * (X / ((K : ℝ) + 1)) := by
      have : (1 + p * (-1 / ((K : ℝ) + 1))) * X = X - p * (X / ((K : ℝ) + 1)) := by ring
      linarith
    calc ∑ m ∈ Finset.Ioc 0 K, (m : ℝ) ^ (p - 1) + X / ((K : ℝ) + 1)
        ≤ (K : ℝ) ^ p / p + X / ((K : ℝ) + 1) := by linarith
      _ ≤ X / p := by
        rw [div_add' _ _ _ hp0.ne', div_le_div_iff_of_pos_right hp0]
        linarith

/-! ## 4. The tail `Σ_{n > a} μ(n)/n²` -/

lemma rpow_div_sq {x : ℝ} (hx : 0 < x) (α : ℝ) : x ^ α / x ^ 2 = x ^ (α - 2) := by
  rw [Real.rpow_sub hx, Real.rpow_two]

lemma rpow_div_cube {x : ℝ} (hx : 0 < x) (α : ℝ) : x ^ α / x ^ 3 = x ^ (α - 3) := by
  rw [Real.rpow_sub hx, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma inv_sq_sub_le {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ (x ^ 2)⁻¹ - ((x + 1) ^ 2)⁻¹ ∧ (x ^ 2)⁻¹ - ((x + 1) ^ 2)⁻¹ ≤ 2 / x ^ 3 := by
  have hx0 : 0 < x := by linarith
  constructor
  · rw [sub_nonneg]
    exact inv_anti₀ (by positivity) (by nlinarith)
  · rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hx0 2, pow_pos hx0 3, pow_pos hx0 4]

theorem g_tail_le {C α : ℝ} (hC : 0 ≤ C) (hα : α < 2)
    (hM : ∀ n : ℕ, 1 ≤ n → |M n| ≤ C * (n : ℝ) ^ α) {a : ℕ} (ha : 1 ≤ a) :
    |∑' i, g (i + (a + 1))| ≤ C * (2 + 2 / (2 - α)) * (a : ℝ) ^ (α - 2) := by
  have hsum : Summable g := hasSum_moebius_div_sq.summable
  have hs' : Summable (fun i => g (i + (a + 1))) := (summable_nat_add_iff (a + 1)).mpr hsum
  set f : ℕ → ℝ := fun n => ((n : ℝ) ^ 2)⁻¹ with hf
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hpart : ∀ L : ℕ, |∑ i ∈ Finset.range L, g (i + (a + 1))| ≤
      C * (2 + 2 / (2 - α)) * (a : ℝ) ^ (α - 2) := by
    intro L
    have e : ∑ i ∈ Finset.range L, g (i + (a + 1)) =
        ∑ i ∈ Finset.range L, (μ (a + 1 + i) : ℝ) * f (a + 1 + i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [g, hf, show i + (a + 1) = a + 1 + i by ring, div_eq_mul_inv]
    rw [e, abel]
    -- the three pieces
    have hp1 : |M (a + L) * f (a + L + 1)| ≤ C * (a : ℝ) ^ (α - 2) := by
      have hn : (0 : ℝ) < ((a + L : ℕ) : ℝ) := by positivity
      rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ f (a + L + 1) from by rw [hf]; positivity)]
      calc |M (a + L)| * f (a + L + 1) ≤ C * ((a + L : ℕ) : ℝ) ^ α * f (a + L) := by
            gcongr
            · exact hM _ (by omega)
            · rw [hf]; push_cast
              exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
        _ = C * ((a + L : ℕ) : ℝ) ^ (α - 2) := by
            rw [hf, mul_assoc, ← div_eq_mul_inv, rpow_div_sq hn]
        _ ≤ C * (a : ℝ) ^ (α - 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hC
            have hle : (a : ℝ) ≤ ((a + L : ℕ) : ℝ) := by
              push_cast; linarith [(L.cast_nonneg : (0:ℝ) ≤ L)]
            exact Real.rpow_le_rpow_of_nonpos ha0 hle (by linarith)
    have hp2 : |M a * f (a + 1)| ≤ C * (a : ℝ) ^ (α - 2) := by
      rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ f (a + 1) from by rw [hf]; positivity)]
      calc |M a| * f (a + 1) ≤ C * (a : ℝ) ^ α * f a := by
            gcongr
            · exact hM _ ha
            · rw [hf]; push_cast
              exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
        _ = C * (a : ℝ) ^ (α - 2) := by
            rw [hf, mul_assoc, ← div_eq_mul_inv, rpow_div_sq ha0]
    have hp3 : |∑ i ∈ Finset.range L, M (a + 1 + i) * (f (a + 1 + i) - f (a + 2 + i))| ≤
        2 * C * ((a : ℝ) ^ (α - 2) / (2 - α)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ Finset.range L, |M (a + 1 + i) * (f (a + 1 + i) - f (a + 2 + i))|
          ≤ ∑ i ∈ Finset.range L, 2 * C * ((a + 1 + i : ℕ) : ℝ) ^ (α - 3) := by
            refine Finset.sum_le_sum fun i _ => ?_
            set n : ℕ := a + 1 + i with hn
            have hn1 : (1 : ℝ) ≤ n := by rw [hn]; push_cast; linarith [(i.cast_nonneg : (0:ℝ) ≤ i)]
            have hn0 : (0 : ℝ) < n := by linarith
            have h2 : a + 2 + i = n + 1 := by omega
            rw [h2]
            obtain ⟨d0, d1⟩ := inv_sq_sub_le hn1
            have hfn : f n - f (n + 1) = ((n : ℝ) ^ 2)⁻¹ - (((n : ℝ) + 1) ^ 2)⁻¹ := by
              simp only [hf]; push_cast; ring
            rw [abs_mul, hfn, abs_of_nonneg d0]
            calc |M n| * (((n : ℝ) ^ 2)⁻¹ - (((n : ℝ) + 1) ^ 2)⁻¹)
                ≤ (C * (n : ℝ) ^ α) * (2 / (n : ℝ) ^ 3) := by
                  gcongr
                  exact hM n (by omega)
              _ = 2 * C * (n : ℝ) ^ (α - 3) := by
                  rw [← rpow_div_cube hn0]; ring
        _ = 2 * C * ∑ i ∈ Finset.range L, ((a + 1 + i : ℕ) : ℝ) ^ (α - 3) := by
            rw [Finset.mul_sum]
        _ ≤ 2 * C * ((a : ℝ) ^ (α - 2) / (2 - α)) := by
            gcongr
            exact sum_rpow_tail_le ha hα L
    have := abs_add_le (M (a + L) * f (a + L + 1) - M a * f (a + 1))
      (∑ i ∈ Finset.range L, M (a + 1 + i) * (f (a + 1 + i) - f (a + 2 + i)))
    have := abs_sub (M (a + L) * f (a + L + 1)) (M a * f (a + 1))
    have e2 : C * (2 + 2 / (2 - α)) * (a : ℝ) ^ (α - 2) =
        C * (a : ℝ) ^ (α - 2) + C * (a : ℝ) ^ (α - 2) + 2 * C * ((a : ℝ) ^ (α - 2) / (2 - α)) := by
      ring
    rw [e2]
    linarith
  have ht := hs'.hasSum.tendsto_sum_nat
  exact le_of_tendsto' ht.abs hpart


/-! ## 5. The hyperbola split: `|Q(N) − 6N/π²| ≤ Y + K·N·Y^{α−2}` -/

lemma floor_div_bounds (N d : ℕ) :
    (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) ∧ ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
  rw [← Nat.floor_div_eq_div (K := ℝ)]
  have h0 : (0 : ℝ) ≤ (N : ℝ) / d := by positivity
  exact ⟨by linarith [Nat.lt_floor_add_one ((N : ℝ) / d)], Nat.floor_le h0⟩

lemma filter_eq_Ioc_sqrt {Y N m : ℕ} (hm : 1 ≤ m) :
    (Finset.Ioc Y N).filter (fun d => m * d ^ 2 ≤ N) = Finset.Ioc Y (Nat.sqrt (N / m)) := by
  have key : ∀ d : ℕ, m * d ^ 2 ≤ N ↔ d ≤ Nat.sqrt (N / m) := by
    intro d; rw [Nat.le_sqrt', Nat.le_div_iff_mul_le hm, mul_comm]
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  rw [key]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    have h4 : m * d ^ 2 ≤ N := (key d).mpr h3
    have h5 : d ≤ d ^ 2 := by nlinarith
    nlinarith

theorem main_bound {C α : ℝ} (hC : 0 ≤ C) (hα0 : 0 ≤ α) (hα : α < 2)
    (hM : ∀ n : ℕ, 1 ≤ n → |M n| ≤ C * (n : ℝ) ^ α) {N Y : ℕ} (hY : 1 ≤ Y) (hYN : Y ≤ N) :
    |(sqfCount N : ℝ) - 6 / Real.pi ^ 2 * N| ≤
      Y + (C * (2 + 2 / (2 - α)) + 2 * C / (1 - α / 2)) * (N * (Y : ℝ) ^ (α - 2)) := by
  have hQ : (sqfCount N : ℝ) = ∑ d ∈ Finset.Ioc 0 N, (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) (sqfCount_eq N)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at this
    rw [this]
    have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by ext n; simp; omega
    rw [hI]
  rw [hQ, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le Y) hYN]
  set S1 := ∑ d ∈ Finset.Ioc 0 Y, (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) with hS1
  set S2 := ∑ d ∈ Finset.Ioc Y N, (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) with hS2
  set T := ∑' i, g (i + (Y + 1)) with hT
  have hG : ∑ d ∈ Finset.Ioc 0 Y, g d = 6 / Real.pi ^ 2 - T := by
    have h1 := hasSum_moebius_div_sq.summable.sum_add_tsum_nat_add (Y + 1)
    rw [hasSum_moebius_div_sq.tsum_eq, sum_range_succ_eq_Ioc g (by simp [g]), ← hT] at h1
    linarith
  -- the fractional parts, `d ≤ Y`
  have hA1 : |S1 - N * ∑ d ∈ Finset.Ioc 0 Y, g d| ≤ Y := by
    have e : S1 - N * ∑ d ∈ Finset.Ioc 0 Y, g d =
        ∑ d ∈ Finset.Ioc 0 Y, (μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / ((d : ℝ) ^ 2)) := by
      rw [hS1, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [g]; ring
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ Finset.Ioc 0 Y, |(μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / ((d : ℝ) ^ 2))|
        ≤ ∑ d ∈ Finset.Ioc 0 Y, (1 : ℝ) := by
          refine Finset.sum_le_sum fun d _ => ?_
          have hb := floor_div_bounds N (d ^ 2)
          push_cast at hb
          rw [abs_mul]
          have hmu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          have h2 : |((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / ((d : ℝ) ^ 2)| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
          calc |(μ d : ℝ)| * |((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / ((d : ℝ) ^ 2)| ≤ 1 * 1 :=
                mul_le_mul hmu h2 (abs_nonneg _) zero_le_one
            _ = 1 := by ring
      _ = Y := by simp
  -- the large `d`, after swapping the order of summation
  have hS2b : |S2| ≤ 2 * C / (1 - α / 2) * (N * (Y : ℝ) ^ (α - 2)) := by
    have hswap : S2 = ∑ m ∈ Finset.Ioc 0 N, ∑ d ∈ Finset.Ioc Y (Nat.sqrt (N / m)), (μ d : ℝ) := by
      have h1 : ∀ d ∈ Finset.Ioc Y N, (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) =
          ∑ m ∈ Finset.Ioc 0 N, if m * d ^ 2 ≤ N then (μ d : ℝ) else 0 := by
        intro d hd
        have hd0 : 0 < d ^ 2 := by
          have : 0 < d := by have := (Finset.mem_Ioc.mp hd).1; omega
          positivity
        have hfil : (Finset.Ioc 0 N).filter (fun m => m * d ^ 2 ≤ N) = Finset.Ioc 0 (N / d ^ 2) := by
          ext m; simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.le_div_iff_mul_le hd0]
          constructor
          · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by nlinarith⟩, h3⟩
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hfil, Nat.card_Ioc, Nat.sub_zero]
        ring
      rw [hS2, Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [← Finset.sum_filter, filter_eq_Ioc_sqrt (Finset.mem_Ioc.mp hm).1]
    rw [hswap]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    set K := N / (Y + 1) ^ 2 with hK
    have hinner : ∀ m ∈ Finset.Ioc 0 N, |∑ d ∈ Finset.Ioc Y (Nat.sqrt (N / m)), (μ d : ℝ)| ≤
        if m ≤ K then 2 * C * ((N : ℝ) / m) ^ (α / 2) else 0 := by
      intro m hm
      have hm1 := (Finset.mem_Ioc.mp hm).1
      by_cases hs : Y < Nat.sqrt (N / m)
      · set s := Nat.sqrt (N / m) with hsdef
        have hmK : m ≤ K := by
          rw [hK, Nat.le_div_iff_mul_le (by positivity)]
          have h1 : (Y + 1) ^ 2 ≤ N / m := Nat.le_sqrt'.mp hs
          have h2 := (Nat.le_div_iff_mul_le hm1).mp h1
          linarith
        simp only [hmK, ↓reduceIte]
        have heq : ∑ d ∈ Finset.Ioc Y s, (μ d : ℝ) = M s - M Y := by
          rw [M_eq_Ioc, M_eq_Ioc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le Y) hs.le]; ring
        rw [heq]
        have hsY : (Y : ℝ) ≤ s := by exact_mod_cast hs.le
        have hs_pow : (s : ℝ) ^ α ≤ ((N : ℝ) / m) ^ (α / 2) := by
          have hs2 : ((s : ℝ)) ^ 2 ≤ (N : ℝ) / m := by
            have h1 : s ^ 2 ≤ N / m := Nat.sqrt_le' _
            have h2 : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
            calc (s : ℝ) ^ 2 = ((s ^ 2 : ℕ) : ℝ) := by push_cast; ring
              _ ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast h1
              _ ≤ _ := h2
          calc (s : ℝ) ^ α = ((s : ℝ) ^ (2 : ℝ)) ^ (α / 2) := by
                rw [← Real.rpow_mul (Nat.cast_nonneg _)]; congr 1; ring
            _ = ((s : ℝ) ^ 2) ^ (α / 2) := by rw [Real.rpow_two]
            _ ≤ _ := Real.rpow_le_rpow (by positivity) hs2 (by linarith)
        have hYs : (Y : ℝ) ^ α ≤ (s : ℝ) ^ α := Real.rpow_le_rpow (Nat.cast_nonneg _) hsY hα0
        have h1 := hM s (by omega)
        have h2 := hM Y hY
        have h3 := mul_le_mul_of_nonneg_left hYs hC
        have h4 := mul_le_mul_of_nonneg_left hs_pow hC
        calc |M s - M Y| ≤ |M s| + |M Y| := abs_sub _ _
          _ ≤ 2 * C * ((N : ℝ) / m) ^ (α / 2) := by linarith
      · push Not at hs
        rw [Finset.Ioc_eq_empty_of_le hs, Finset.sum_empty, abs_zero]
        split_ifs
        · exact mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg (by positivity) _)
        · exact le_rfl
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hY0 : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
    have hcoef : 0 ≤ 2 * C * (N : ℝ) ^ (α / 2) :=
      mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg hN0.le _)
    have hKle : (K : ℝ) ≤ (N : ℝ) / (Y : ℝ) ^ 2 := by
      have h1 : (K : ℝ) ≤ (N : ℝ) / (((Y + 1) ^ 2 : ℕ) : ℝ) := by rw [hK]; exact Nat.cast_div_le
      refine h1.trans ?_
      push_cast
      exact div_le_div_of_nonneg_left hN0.le (by positivity) (by nlinarith)
    calc ∑ m ∈ Finset.Ioc 0 N, |∑ d ∈ Finset.Ioc Y (Nat.sqrt (N / m)), (μ d : ℝ)|
        ≤ ∑ m ∈ Finset.Ioc 0 N, (if m ≤ K then 2 * C * ((N : ℝ) / m) ^ (α / 2) else 0) :=
          Finset.sum_le_sum hinner
      _ = ∑ m ∈ Finset.Ioc 0 K, 2 * C * ((N : ℝ) / m) ^ (α / 2) := by
          rw [← Finset.sum_filter]
          congr 1
          ext m; simp only [Finset.mem_filter, Finset.mem_Ioc]
          constructor
          · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans (Nat.div_le_self _ _)⟩, h3⟩
      _ = 2 * C * (N : ℝ) ^ (α / 2) * ∑ m ∈ Finset.Ioc 0 K, (m : ℝ) ^ ((1 - α / 2) - 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m hm => ?_
          have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Ioc.mp hm).1
          rw [Real.div_rpow (Nat.cast_nonneg _) hm0.le, show (1 - α / 2) - 1 = -(α / 2) by ring,
            Real.rpow_neg hm0.le]
          ring
      _ ≤ 2 * C * (N : ℝ) ^ (α / 2) * ((K : ℝ) ^ (1 - α / 2) / (1 - α / 2)) :=
          mul_le_mul_of_nonneg_left (sum_rpow_head_le (by linarith) (by linarith) K) hcoef
      _ ≤ 2 * C * (N : ℝ) ^ (α / 2) * (((N : ℝ) / (Y : ℝ) ^ 2) ^ (1 - α / 2) / (1 - α / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          exact div_le_div_of_nonneg_right
            (Real.rpow_le_rpow (Nat.cast_nonneg _) hKle (by linarith)) (by linarith)
      _ = 2 * C / (1 - α / 2) * (N * (Y : ℝ) ^ (α - 2)) := by
          rw [Real.div_rpow hN0.le (by positivity), ← Real.rpow_two, ← Real.rpow_mul hY0.le]
          have e1 : (N : ℝ) ^ (α / 2) * (N : ℝ) ^ (1 - α / 2) = N := by
            rw [← Real.rpow_add hN0]; norm_num
          have e2 : (Y : ℝ) ^ (α - 2) = ((Y : ℝ) ^ (2 * (1 - α / 2)))⁻¹ := by
            rw [← Real.rpow_neg hY0.le]; congr 1; ring
          rw [e2]
          linear_combination (2 * C / (1 - α / 2) * ((Y : ℝ) ^ (2 * (1 - α / 2)))⁻¹) * e1
  -- the tail `Σ_{d > Y} μ(d)/d²`
  have hTb := g_tail_le hC hα hM hY
  rw [← hT] at hTb
  have hNT : |(N : ℝ) * T| ≤ C * (2 + 2 / (2 - α)) * (N * (Y : ℝ) ^ (α - 2)) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc (N : ℝ) * |T| ≤ N * (C * (2 + 2 / (2 - α)) * (Y : ℝ) ^ (α - 2)) :=
          mul_le_mul_of_nonneg_left hTb (Nat.cast_nonneg _)
      _ = _ := by ring
  have e : S1 + S2 - 6 / Real.pi ^ 2 * N =
      (S1 - N * ∑ d ∈ Finset.Ioc 0 Y, g d) - N * T + S2 := by
    rw [hG]; ring
  rw [e]
  have t1 := abs_add_le ((S1 - N * ∑ d ∈ Finset.Ioc 0 Y, g d) - N * T) S2
  have t2 := abs_sub (S1 - N * ∑ d ∈ Finset.Ioc 0 Y, g d) (N * T)
  have e3 : (Y : ℝ) + (C * (2 + 2 / (2 - α)) + 2 * C / (1 - α / 2)) * (N * (Y : ℝ) ^ (α - 2)) =
      Y + C * (2 + 2 / (2 - α)) * (N * (Y : ℝ) ^ (α - 2)) +
        2 * C / (1 - α / 2) * (N * (Y : ℝ) ^ (α - 2)) := by ring
  rw [e3]
  linarith

/-! ## 6. Choosing `Y = ⌊N^{1/(3−α)}⌋` -/

theorem bound_pow {C α : ℝ} (hC : 0 ≤ C) (hα0 : 0 ≤ α) (hα : α < 2)
    (hM : ∀ n : ℕ, 1 ≤ n → |M n| ≤ C * (n : ℝ) ^ α) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      |(sqfCount N : ℝ) - 6 / Real.pi ^ 2 * N| ≤ K * (N : ℝ) ^ (1 / (3 - α)) := by
  set β := 1 / (3 - α) with hβ
  set K1 := C * (2 + 2 / (2 - α)) + 2 * C / (1 - α / 2) with hK1
  have hK10 : 0 ≤ K1 := by
    have a1 : 0 ≤ 2 / (2 - α) := div_nonneg (by norm_num) (by linarith)
    have a2 : 0 ≤ 2 * C / (1 - α / 2) := div_nonneg (by linarith) (by linarith)
    have a3 : 0 ≤ C * (2 + 2 / (2 - α)) := mul_nonneg hC (by linarith)
    linarith
  have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ (2 - α) := Real.rpow_nonneg (by norm_num) _
  refine ⟨1 + K1 * (2 : ℝ) ^ (2 - α), by nlinarith, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hβ0 : 0 < β := by rw [hβ]; apply div_pos one_pos; linarith
  have hβ1 : β ≤ 1 := by rw [hβ, div_le_one (by linarith)]; linarith
  set t := (N : ℝ) ^ β with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hN1 hβ0.le
  have htN : t ≤ N := by
    calc t ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hβ1
      _ = N := Real.rpow_one _
  set Y := ⌊t⌋₊ with hY
  have hY1 : 1 ≤ Y := Nat.le_floor (by exact_mod_cast ht1)
  have hYt : (Y : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hYr : (1 : ℝ) ≤ Y := by exact_mod_cast hY1
  have hYt2 : t / 2 ≤ Y := by
    have := Nat.lt_floor_add_one t
    linarith
  have hYN : Y ≤ N := by exact_mod_cast hYt.trans htN
  have hmain := main_bound hC hα0 hα hM hY1 hYN
  rw [← hK1] at hmain
  have hNY : (N : ℝ) * (Y : ℝ) ^ (α - 2) ≤ (2 : ℝ) ^ (2 - α) * t := by
    have h1 : (Y : ℝ) ^ (α - 2) ≤ (t / 2) ^ (α - 2) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hYt2 (by linarith)
    have h2 : (t / 2) ^ (α - 2) = t ^ (α - 2) * (2 : ℝ) ^ (2 - α) := by
      rw [Real.div_rpow (by linarith) (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
      congr 2; ring
    have h3 : (N : ℝ) * t ^ (α - 2) = t := by
      rw [ht, ← Real.rpow_mul hN0.le]
      have : (N : ℝ) * (N : ℝ) ^ (β * (α - 2)) = (N : ℝ) ^ (1 + β * (α - 2)) := by
        rw [Real.rpow_add hN0, Real.rpow_one]
      rw [this]
      congr 1
      have h3a : (3 - α) ≠ 0 := by linarith
      rw [hβ]; field_simp; ring
    calc (N : ℝ) * (Y : ℝ) ^ (α - 2) ≤ N * (t / 2) ^ (α - 2) :=
          mul_le_mul_of_nonneg_left h1 hN0.le
      _ = (2 : ℝ) ^ (2 - α) * t := by rw [h2, ← mul_assoc, h3]; ring
  have h4 := mul_le_mul_of_nonneg_left hNY hK10
  calc _ ≤ (Y : ℝ) + K1 * (N * (Y : ℝ) ^ (α - 2)) := hmain
    _ ≤ t + K1 * ((2 : ℝ) ^ (2 - α) * t) := by linarith
    _ = (1 + K1 * (2 : ℝ) ^ (2 - α)) * t := by ring

/-! ## 7. The theorems -/

/-- **Möbius bound ⇒ squarefree error.** If `Σ_{n≤N} μ(n) ≪ N^{θ+ε}` for every `ε > 0` (`0 ≤ θ ≤ 1`),
then `Q(x) − 6x/π² ≪ x^{1/(3−θ)+ε}` for every `ε > 0`. -/
theorem squarefreeError_of_moebius {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h : FleetHeadContour.MoebiusSumBound θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(Q x : ℝ) - 6 * x / Real.pi ^ 2| ≤ C * x ^ (1 / (3 - θ) + ε) := by
  intro ε hε
  set ε' := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨C, hC⟩ := h ε' hε'0
  have hM : ∀ n : ℕ, 1 ≤ n → |M n| ≤ C * (n : ℝ) ^ (θ + ε') := fun n hn => hC n hn
  have hC0 : 0 ≤ C := by
    have := hM 1 le_rfl
    rw [Nat.cast_one, Real.one_rpow, mul_one] at this
    exact (abs_nonneg _).trans this
  obtain ⟨K, hK0, hK⟩ := bound_pow hC0 (by linarith) (by linarith) hM
  have hexp : 1 / (3 - (θ + ε')) ≤ 1 / (3 - θ) + ε := by
    have e : 1 / (3 - (θ + ε')) - 1 / (3 - θ) = ε' / ((3 - θ) * (3 - (θ + ε'))) := by
      have h1 : (3 - θ) ≠ 0 := by linarith
      have h2 : (3 - (θ + ε')) ≠ 0 := by linarith
      field_simp; ring
    have h3 : 3 ≤ (3 - θ) * (3 - (θ + ε')) := by nlinarith
    have : ε' / ((3 - θ) * (3 - (θ + ε'))) ≤ ε' / 3 :=
      div_le_div_of_nonneg_left hε'0.le (by norm_num) h3
    linarith
  refine ⟨K + 1, fun x hx => ?_⟩
  set N := ⌊x⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hQ : (Q x : ℝ) = sqfCount N := rfl
  have hb := hK N hN
  have hpi : 6 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have hpi0 : 0 ≤ 6 / Real.pi ^ 2 := by positivity
  have hexp0 : 0 ≤ 1 / (3 - θ) + ε := add_nonneg (div_nonneg zero_le_one (by linarith)) hε.le
  have ht : (N : ℝ) ^ (1 / (3 - (θ + ε'))) ≤ x ^ (1 / (3 - θ) + ε) := by
    calc (N : ℝ) ^ (1 / (3 - (θ + ε'))) ≤ x ^ (1 / (3 - (θ + ε'))) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hNx (div_nonneg zero_le_one (by linarith))
      _ ≤ x ^ (1 / (3 - θ) + ε) := Real.rpow_le_rpow_of_exponent_le hx hexp
  have hx1 : 1 ≤ x ^ (1 / (3 - θ) + ε) := Real.one_le_rpow hx hexp0
  rw [hQ]
  have e : (sqfCount N : ℝ) - 6 * x / Real.pi ^ 2 =
      ((sqfCount N : ℝ) - 6 / Real.pi ^ 2 * N) - 6 / Real.pi ^ 2 * (x - N) := by ring
  rw [e]
  have h6 : |6 / Real.pi ^ 2 * (x - N)| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hpi0 (by linarith))]
    nlinarith
  have h7 := mul_le_mul_of_nonneg_left ht hK0
  calc _ ≤ |(sqfCount N : ℝ) - 6 / Real.pi ^ 2 * N| + |6 / Real.pi ^ 2 * (x - N)| := abs_sub _ _
    _ ≤ K * x ^ (1 / (3 - θ) + ε) + x ^ (1 / (3 - θ) + ε) := by linarith
    _ = (K + 1) * x ^ (1 / (3 - θ) + ε) := by ring

open FleetHeadContour Reduction in
/-- **Quasi-RH ⇒ `Q(x) − 6x/π² ≪ x^{8/17+ε}`.** Under `QuasiRHWiring.QuasiRH` (`ζ(s) ≠ 0` for
`Re s > 7/8`, carried as a hypothesis): `Σ μ ≪ N^{7/8+ε}` (`landauTransfer`), then `θ = 7/8`. -/
theorem squarefreeError_of_quasiRH (hQ : QuasiRHWiring.QuasiRH) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(Q x : ℝ) - 6 * x / Real.pi ^ 2| ≤ C * x ^ (8 / 17 + ε) := by
  have hM : MoebiusSumBound (7 / 8) := by
    have := landauTransfer (3 / 8) (by norm_num) (by norm_num) (stripBound_of_quasiRH hQ)
    rwa [show (1 / 2 + 3 / 8 : ℝ) = 7 / 8 by norm_num] at this
  have h := squarefreeError_of_moebius (by norm_num) (by norm_num) hM
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun x hx => ?_⟩
  have := hC x hx
  rwa [show (1 : ℝ) / (3 - 7 / 8) = 8 / 17 by norm_num] at this

open FleetHeadContour Reduction in
/-- **RH ⇒ `Q(x) − 6x/π² ≪ x^{2/5+ε}`** (`θ = 1/2`, via Littlewood's theorem `landauTransfer 0`). -/
theorem squarefreeError_of_RH (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(Q x : ℝ) - 6 * x / Real.pi ^ 2| ≤ C * x ^ (2 / 5 + ε) := by
  have hs : StripBound 0 := fun ρ hρ => by
    rw [riemannHypothesis_iff.mp hRH ρ hρ]; simp
  have hM : MoebiusSumBound (1 / 2) := by
    have := landauTransfer 0 le_rfl (by norm_num) hs
    rwa [add_zero] at this
  have h := squarefreeError_of_moebius (by norm_num) (by norm_num) hM
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun x hx => ?_⟩
  have := hC x hx
  rwa [show (1 : ℝ) / (3 - 1 / 2) = 2 / 5 by norm_num] at this

end FleetSquarefreeError
