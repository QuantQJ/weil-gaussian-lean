import FleetHeadContourStrip
import ZetaStrip
import ZeroSymmetry
import QuasiRHWiring

/-!
# The converse of the window–strip theorem, and the optimal window rate

`zeros_in_strip_of_window_rate`: `W(c)` (window `≤ C e^{c/b}` at every `|α| ≥ 1/2`, `C` per `α`) ⇒
`D ≤ √(2c)`, where `D = sup |Re ρ − 1/2|` over the nontrivial zeros. This module asks for the converse.

## What is proved here

* `headWindow_le_unconditional` : window `≤ 8√π e^{(11/10)/b}`, every `α`, `0 < b ≤ 1`, no hypothesis
  (from `‖M_N(1/2+it)‖ ≤ 2√N` and `N = cut b ≤ e^{1.1/b}`). So `W(11/10)` holds unconditionally, with `C`
  uniform in `α` (`windowRate_eleven_tenths`). The strip it gives, `√(11/5) > 1/2`, is vacuous: the strip
  theorem says something only for `c < 1/8`.
* `windowRate_of_moebiusSumBound` : `Σ_{n≤N} μ(n) ≪ N^{θ+ε}` (`θ ≥ 1/2`) ⇒ `W((11/5)(θ−1/2) + ε)` for every
  `ε > 0` (partial summation on the critical line; `C` depends on `α`, through `(1+|α|)²`).
* `windowRate_of_strip` : strip of half-width `δ` ⇒ `W((11/5)δ + ε)`, given `LandauTransfer δ`
  (strip `δ` ⇒ `Σ_{n≤N} μ(n) ≪ N^{1/2+δ+ε}`); for `δ = 0` this is Littlewood's theorem (Titchmarsh §14.25),
  for general `δ` the same proof. Here the transfer is a named hypothesis; it is proved for every `0 ≤ δ < 1/2` as
  `FleetHeadContour.landauTransfer` in `FleetLandauTransfer.lean`, which also gives the hypothesis-free
  `windowRate_of_strip'`, `RH_iff_windowSubexp'` and `windowRate_of_quasiRH'`.
* `RH_iff_windowSubexp` : given `LandauTransfer 0` (Littlewood's theorem), `RH ↔ WindowSubexpBound`.
* `windowRate_of_quasiRH` : the `δ = 3/8` instance under `QuasiRHWiring.QuasiRH`: rate `33/40 + ε`.
* `zeroDev_sq_half_le_windowRateInf`, `windowRateInf_bounds` : with `c* = inf {c ≥ 0 | W(c)}`,
  `D²/2 ≤ c* ≤ 11/10` unconditionally, and `c* ≤ (11/5) D` given `LandauTransfer D`.
* `not_windowRate_of_lt` : no rate `c < D²/2` (when `c ≥ 0` or `D > 0`); `windowSubexp_iff_windowRateInf_eq_zero`.

## Why the exponent is `(11/5)δ`, not `δ²/2`

The window sees two different things. Its Gaussian smoothing sees a zero `ρ = 1/2 + δ + iγ` through
`|Σ μ(n) n^{-1/2-iα} e^{-b log² n}|² ≈ e^{(δ² − (γ−α)²)/(2b)}`: that is the `D²/2` of the strip theorem.
Its sharp cutoff at `N = e^{1.1/b}` sees the same zero through the explicit formula for the Möbius partial
sums, whose term `N^{ρ−s}/((ρ−s)ζ'(ρ))` has size `N^{δ} = e^{1.1δ/b}` at every height `α`; squared, `e^{2.2δ/b}`.
For `0 < δ ≤ 1/2`, `(11/5)δ > δ²/2`, so if a zero off the line existed the window would be expected to grow
at rate `(11/5)D` (the lower-bound half of this is Landau's Ω-theorem adapted to the window; heuristic,
not proved here), and a converse with `c = δ²/2` cannot be a theorem short of RH. At `δ = 0` both
forms agree: RH gives every `c > 0` (via Littlewood), and `c = 0` (window bounded) is not known under RH.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real
open OffLineDetection Reduction ZeroSumLimit GaussianTest

namespace FleetHeadContour

/-- The window integral `∫ ‖M_{cut b}(1/2+it)‖² e^{-(t−α)²/(4b)} dt`. -/
def headWindow (b α : ℝ) : ℝ :=
  ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
    * Real.exp (-(t - α) ^ 2 / (4 * b))

/-- `W(c)`: the hypothesis of `zeros_in_strip_of_window_rate` at rate `c` (the constant may depend on `α`). -/
def WindowRate (c : ℝ) : Prop :=
  ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 → headWindow b α ≤ C * Real.exp (c / b)

/-- `D = sup |Re ρ − 1/2|` over the nontrivial zeros. -/
def zeroDev : ℝ := sSup {d : ℝ | ∃ ρ : ℂ, IsNontrivialZero ρ ∧ d = |ρ.re - 1 / 2|}

/-- The optimal window rate `inf {c ≥ 0 | W(c)}`. -/
def windowRateInf : ℝ := sInf {c : ℝ | 0 ≤ c ∧ WindowRate c}

/-! ## The deviation `D` -/

lemma abs_re_sub_half_lt {ρ : ℂ} (hρ : IsNontrivialZero ρ) : |ρ.re - 1 / 2| < 1 / 2 := by
  obtain ⟨h0, h1⟩ := ZetaStrip.mem_strip_of_isNontrivialZero hρ
  rw [abs_lt]; constructor <;> linarith

lemma bddAbove_dev : BddAbove {d : ℝ | ∃ ρ : ℂ, IsNontrivialZero ρ ∧ d = |ρ.re - 1 / 2|} :=
  ⟨1 / 2, by rintro d ⟨ρ, hρ, rfl⟩; exact (abs_re_sub_half_lt hρ).le⟩

theorem le_zeroDev {ρ : ℂ} (hρ : IsNontrivialZero ρ) : |ρ.re - 1 / 2| ≤ zeroDev :=
  le_csSup bddAbove_dev ⟨ρ, hρ, rfl⟩

theorem zeroDev_nonneg : 0 ≤ zeroDev :=
  Real.sSup_nonneg (by rintro d ⟨ρ, _, rfl⟩; exact abs_nonneg _)

theorem zeroDev_le_iff {d : ℝ} (hd : 0 ≤ d) :
    zeroDev ≤ d ↔ ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.re - 1 / 2| ≤ d := by
  constructor
  · intro h ρ hρ; exact (le_zeroDev hρ).trans h
  · intro h; exact Real.sSup_le (by rintro e ⟨ρ, hρ, rfl⟩; exact h ρ hρ) hd

theorem zeroDev_le_half : zeroDev ≤ 1 / 2 :=
  (zeroDev_le_iff (by norm_num)).mpr fun _ hρ => (abs_re_sub_half_lt hρ).le

theorem RH_iff_zeroDev_eq_zero : RiemannHypothesis ↔ zeroDev = 0 := by
  rw [riemannHypothesis_iff]
  constructor
  · intro h
    refine le_antisymm ((zeroDev_le_iff le_rfl).mpr fun ρ hρ => ?_) zeroDev_nonneg
    rw [h ρ hρ]; simp
  · intro h ρ hρ
    have := le_zeroDev hρ
    rw [h] at this
    have h0 := abs_nonneg (ρ.re - 1 / 2)
    have : |ρ.re - 1 / 2| = 0 := le_antisymm this h0
    rw [abs_eq_zero] at this; linarith

/-! ## Window rates: monotonicity and the strip theorem -/

theorem windowRate_mono {c c' : ℝ} (hcc : c ≤ c') (h : WindowRate c) : WindowRate c' := by
  intro α hα
  obtain ⟨C, hC⟩ := h α hα
  refine ⟨|C|, fun b hb hb1 => (hC b hb hb1).trans ?_⟩
  have e : Real.exp (c / b) ≤ Real.exp (c' / b) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hcc hb.le)
  calc C * Real.exp (c / b) ≤ |C| * Real.exp (c / b) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * Real.exp (c' / b) := mul_le_mul_of_nonneg_left e (abs_nonneg C)

/-- `W(c) ⇒ D ≤ √(2c)` (`zeros_in_strip_of_window_rate`, restated through `D`). -/
theorem zeroDev_le_of_windowRate {c : ℝ} (hc : 0 ≤ c) (h : WindowRate c) :
    zeroDev ≤ Real.sqrt (2 * c) := by
  have hs := zeros_in_strip_of_window_rate hc h
  refine (zeroDev_le_iff (Real.sqrt_nonneg _)).mpr fun ρ hρ => ?_
  obtain ⟨x, hx⟩ := multEnum_canonical.exists_index hρ
  rw [← hx]; exact hs x

theorem windowSubexp_iff_forall_windowRate : WindowSubexpBound ↔ ∀ c : ℝ, 0 < c → WindowRate c := by
  constructor
  · intro h c hc α hα; exact h α hα c hc
  · intro h α hα c hc; exact h c hc α hα

/-! ## The unconditional rate `c = 11/10` -/

lemma two_sqrt_step (N : ℕ) :
    2 * Real.sqrt N + ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) ≤ 2 * Real.sqrt ((N : ℝ) + 1) := by
  set x := Real.sqrt N with hx
  set y := Real.sqrt ((N : ℝ) + 1) with hy
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 < y := Real.sqrt_pos.mpr (by positivity)
  have hxx : x ^ 2 = N := Real.sq_sqrt (by positivity)
  have hyy : y ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hr : ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) = 1 / y := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, hy, one_div]
  rw [hr]
  have key : 2 * x * y + 1 ≤ 2 * y ^ 2 := by nlinarith [sq_nonneg (y - x)]
  have : 2 * x + 1 / y = (2 * x * y + 1) / y := by field_simp
  rw [this, div_le_iff₀ hy0]
  nlinarith

/-- `‖M_N(1/2+it)‖ ≤ 2√N`. -/
theorem norm_Mpoly_half_le (N : ℕ) (t : ℝ) :
    ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ 2 * Real.sqrt N := by
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + t * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have hterm : ∀ m : ℕ, 1 ≤ m →
      ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)‖ ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro m hm
    rw [norm_mul, norm_natCast_cpow_of_pos (by omega)]
    have h1 : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
      have := FleetMollifierTail.moebius_abs_le m
      rw [show (ArithmeticFunction.moebius m : ℂ) = ((ArithmeticFunction.moebius m : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs]
      exact this
    have e : (-s).re = -(1 / 2 : ℝ) := by simp [hre]
    rw [e]
    calc ‖(ArithmeticFunction.moebius m : ℂ)‖ * (m : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ 1 * (m : ℝ) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := one_mul _
  have hsum : ∀ N : ℕ, ∑ m ∈ Finset.range (N + 1),
      ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)‖ ≤ 2 * Real.sqrt N := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h := hterm (n + 1) (by omega)
      have hst := two_sqrt_step n
      push_cast at h ⊢
      linarith
  exact (norm_sum_le _ _).trans (hsum N)

/-- **Unconditional window bound**: `∫ ‖M_{cut b}(1/2+it)‖² e^{-(t−α)²/(4b)} dt ≤ 8√π e^{(11/10)/b}`
for every `α` and `0 < b ≤ 1` (the constant does not depend on `α`). -/
theorem headWindow_le_unconditional {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α : ℝ) :
    headWindow b α ≤ 8 * Real.sqrt π * Real.exp ((11 / 10) / b) := by
  set N := FleetFiniteHeadRH.cut b with hN
  have hNe : (N : ℝ) ≤ Real.exp (11 / (10 * b)) := cut_le
  have hE : Real.exp (11 / (10 * b)) = Real.exp ((11 / 10) / b) := by congr 1; field_simp
  rw [hE] at hNe
  set E := Real.exp ((11 / 10) / b)
  have hpt : ∀ t : ℝ, ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))
      ≤ (4 * E) * Real.exp (-(t - α) ^ 2 / (4 * b)) := by
    intro t
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have h := norm_Mpoly_half_le N t
    have h2 : ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 ≤ (2 * Real.sqrt N) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at h2
    linarith
  have hint := integral_mono (integrable_M_window hb N α)
    ((integrable_gauss_scale (d := 4 * b) (by positivity) α).const_mul (4 * E)) hpt
  rw [integral_const_mul, integral_gauss_scale (by positivity)] at hint
  have hs : Real.sqrt (π * (4 * b)) ≤ 2 * Real.sqrt π := by
    calc Real.sqrt (π * (4 * b)) ≤ Real.sqrt (π * 4) :=
          Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
      _ = 2 * Real.sqrt π := by
          rw [Real.sqrt_mul Real.pi_pos.le, show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]; ring
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  unfold headWindow
  calc _ ≤ 4 * E * Real.sqrt (π * (4 * b)) := hint
    _ ≤ 4 * E * (2 * Real.sqrt π) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem windowRate_eleven_tenths : WindowRate (11 / 10) :=
  fun α _ => ⟨8 * Real.sqrt π, fun _ hb hb1 => headWindow_le_unconditional hb hb1 α⟩

/-! ## The optimal rate -/

lemma rateSet_nonempty : (11 / 10 : ℝ) ∈ {c : ℝ | 0 ≤ c ∧ WindowRate c} :=
  ⟨by norm_num, windowRate_eleven_tenths⟩

lemma rateSet_bddBelow : BddBelow {c : ℝ | 0 ≤ c ∧ WindowRate c} := ⟨0, fun _ h => h.1⟩

theorem windowRateInf_le_of_windowRate {c : ℝ} (hc : 0 ≤ c) (h : WindowRate c) : windowRateInf ≤ c :=
  csInf_le rateSet_bddBelow ⟨hc, h⟩

theorem windowRateInf_le_eleven_tenths : windowRateInf ≤ 11 / 10 :=
  windowRateInf_le_of_windowRate (by norm_num) windowRate_eleven_tenths

theorem windowRateInf_nonneg : 0 ≤ windowRateInf :=
  le_csInf ⟨_, rateSet_nonempty⟩ fun _ h => h.1

/-- Every rate above the infimum is attained (the rate set is upward closed). -/
theorem windowRate_of_windowRateInf_lt {c : ℝ} (hc : windowRateInf < c) : WindowRate c := by
  obtain ⟨c₀, ⟨_, h₀⟩, hlt⟩ := exists_lt_of_csInf_lt ⟨_, rateSet_nonempty⟩ hc
  exact windowRate_mono hlt.le h₀

/-- **Lower bound for the optimal rate**: `D²/2 ≤ inf {c | W(c)}`. -/
theorem zeroDev_sq_half_le_windowRateInf : zeroDev ^ 2 / 2 ≤ windowRateInf := by
  refine le_csInf ⟨_, rateSet_nonempty⟩ fun c ⟨hc, h⟩ => ?_
  have h1 := zeroDev_le_of_windowRate hc h
  have h2 : zeroDev ^ 2 ≤ 2 * c := by
    calc zeroDev ^ 2 ≤ Real.sqrt (2 * c) ^ 2 := pow_le_pow_left₀ zeroDev_nonneg h1 2
      _ = 2 * c := Real.sq_sqrt (by positivity)
  linarith

theorem windowSubexp_iff_windowRateInf_eq_zero : WindowSubexpBound ↔ windowRateInf = 0 := by
  rw [windowSubexp_iff_forall_windowRate]
  constructor
  · intro h
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) windowRateInf_nonneg
    rw [zero_add]; exact windowRateInf_le_of_windowRate hε.le (h ε hε)
  · intro h c hc
    exact windowRate_of_windowRateInf_lt (by rw [h]; exact hc)

theorem RH_of_windowRateInf_eq_zero (h : windowRateInf = 0) : RiemannHypothesis :=
  RH_of_window_subexp (windowSubexp_iff_windowRateInf_eq_zero.mpr h)

/-! ## Partial summation: a Möbius partial-sum bound gives a window rate -/

/-- `|Σ_{n ≤ N} μ(n)| ≤ C_ε N^{θ+ε}` for every `ε > 0` (`N ≥ 1`). -/
def MoebiusSumBound (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.moebius n : ℝ)| ≤ C * (N : ℝ) ^ (θ + ε)

/-- Abel summation on `range (N+1)`. -/
lemma abel_range (a f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), a n * f n
      = (∑ k ∈ Finset.range (N + 1), a k) * f N
        - ∑ n ∈ Finset.range N, (∑ k ∈ Finset.range (n + 1), a k) * (f (n + 1) - f n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih,
      Finset.sum_range_succ (fun n => (∑ k ∈ Finset.range (n + 1), a k) * (f (n + 1) - f n)),
      Finset.sum_range_succ (fun k => a k) (N + 1)]
    ring

/-- `‖(n+1)^{-s} − n^{-s}‖ ≤ ‖s‖ n^{-Re s − 1}` for `n ≥ 1`, `Re s ≥ −1`. -/
lemma norm_cpow_succ_sub_le (s : ℂ) (hs : -1 ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖((n + 1 : ℕ) : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (-s) with hg
  have hd : ∀ x ∈ Icc (n : ℝ) (n + 1),
      HasDerivWithinAt g (-s * (x : ℂ) ^ (-s - 1)) (Icc (n : ℝ) (n + 1)) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hn0 hx.1
    exact ((Complex.hasStrictDerivAt_cpow_const (c := -s)
      (Complex.ofReal_mem_slitPlane.mpr hx0)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hbd : ∀ x ∈ Ico (n : ℝ) (n + 1), ‖-s * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hn0 hx.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have e : (-s - 1).re = -s.re - 1 := by simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hn0 hx.1 (by linarith)) (norm_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hbd ((n : ℝ) + 1) ⟨by linarith, le_rfl⟩
  simp only [hg] at h
  rw [show (n : ℝ) + 1 - n = 1 by ring, mul_one] at h
  push_cast at h ⊢
  exact h

/-- **Partial summation on the critical line.** If `|Σ_{k≤n} μ(k)| ≤ K n^{θ'}` for `n ≥ 1` (`θ' ≥ 1/2`), then
`‖M_N(1/2+it)‖ ≤ |K| (1+|t|) (2 + log N) N^{θ'−1/2}`. -/
theorem norm_Mpoly_half_le_of_moebius {K θ' : ℝ} (hθ' : 1 / 2 ≤ θ')
    (hA : ∀ n : ℕ, 1 ≤ n →
      |∑ k ∈ Finset.range (n + 1), (ArithmeticFunction.moebius k : ℝ)| ≤ K * (n : ℝ) ^ θ')
    {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ |K| * ((1 + |t|) * (2 + Real.log N)) * (N : ℝ) ^ (θ' - 1 / 2) := by
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + t * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have hsn : ‖s‖ ≤ 1 + |t| := by
    calc ‖s‖ ≤ ‖((1 / 2 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 1 / 2 + |t| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      _ ≤ 1 + |t| := by linarith
  set A : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (n + 1), (ArithmeticFunction.moebius k : ℝ) with hAdef
  have hA' : ∀ n : ℕ, 1 ≤ n → |A n| ≤ |K| * (n : ℝ) ^ θ' := fun n hn =>
    (hA n hn).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
  have hA0 : A 0 = 0 := by simp [hAdef]
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-s) with hf
  have hcast : ∀ n, (∑ k ∈ Finset.range (n + 1), (ArithmeticFunction.moebius k : ℂ)) = ((A n : ℝ) : ℂ) := by
    intro n; simp [hAdef]
  have habel := abel_range (fun n => (ArithmeticFunction.moebius n : ℂ)) f N
  have hM : Mpoly N s = ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.moebius n : ℂ) * f n := rfl
  rw [hM, habel]
  simp only [hcast]
  set P := (N : ℝ) ^ (θ' - 1 / 2) with hP
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hfN : ‖f N‖ = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simp only [hf]; rw [norm_natCast_cpow_of_pos (by omega)]; congr 1; simp [hre]
  have t1 : ‖((A N : ℝ) : ℂ) * f N‖ ≤ |K| * P := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hfN]
    calc |A N| * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ |K| * (N : ℝ) ^ θ' * (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (hA' N hN) (by positivity)
      _ = |K| * P := by rw [mul_assoc, ← Real.rpow_add hNpos, hP, sub_eq_add_neg]
  have t2 : ∀ n ∈ Finset.range N,
      ‖((A n : ℝ) : ℂ) * (f (n + 1) - f n)‖ ≤ |K| * (1 + |t|) * P * (n : ℝ)⁻¹ := by
    intro n hn
    have hnN : n ≤ N := (Finset.mem_range.mp hn).le
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · simp [hA0]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hd := norm_cpow_succ_sub_le s (by rw [hre]; norm_num) (n := n) hn1
    rw [hre] at hd
    have hpow : (n : ℝ) ^ θ' * (n : ℝ) ^ (-(1 / 2 : ℝ) - 1) ≤ P * (n : ℝ)⁻¹ := by
      rw [← Real.rpow_add hn0, show θ' + (-(1 / 2 : ℝ) - 1) = (θ' - 1 / 2) + (-1) by ring,
        Real.rpow_add hn0, Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hn0.le (by exact_mod_cast hnN) (by linarith)) (by positivity)
    have hd' : ‖f (n + 1) - f n‖ ≤ ‖s‖ * (n : ℝ) ^ (-(1 / 2 : ℝ) - 1) := by
      simp only [hf]; push_cast at hd ⊢; exact hd
    calc |A n| * ‖f (n + 1) - f n‖
        ≤ (|K| * (n : ℝ) ^ θ') * (‖s‖ * (n : ℝ) ^ (-(1 / 2 : ℝ) - 1)) :=
          mul_le_mul (hA' n hn1) hd' (norm_nonneg _) (by positivity)
      _ = (|K| * ‖s‖) * ((n : ℝ) ^ θ' * (n : ℝ) ^ (-(1 / 2 : ℝ) - 1)) := by ring
      _ ≤ (|K| * (1 + |t|)) * (P * (n : ℝ)⁻¹) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsn (abs_nonneg _)) hpow (by positivity) (by positivity)
      _ = _ := by ring
  have hharm : ∑ n ∈ Finset.range N, (n : ℝ)⁻¹ ≤ 1 + Real.log N := by
    have h1 : ∑ n ∈ Finset.range N, (n : ℝ)⁻¹ ≤ ∑ n ∈ Finset.range (N + 1), (n : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        (fun _ _ _ => by positivity)
    have hH : ∑ m ∈ Finset.range (N + 1), (m : ℝ)⁻¹ = (harmonic N : ℝ) := by
      rw [Finset.sum_range_succ']; simp [harmonic]
    linarith [harmonic_le_one_add_log N]
  have hP0 : 0 ≤ P := by positivity
  have hKP : 0 ≤ |K| * P * |t| := by positivity
  calc ‖((A N : ℝ) : ℂ) * f N - ∑ n ∈ Finset.range N, ((A n : ℝ) : ℂ) * (f (n + 1) - f n)‖
      ≤ ‖((A N : ℝ) : ℂ) * f N‖ + ‖∑ n ∈ Finset.range N, ((A n : ℝ) : ℂ) * (f (n + 1) - f n)‖ :=
        norm_sub_le _ _
    _ ≤ |K| * P + ∑ n ∈ Finset.range N, |K| * (1 + |t|) * P * (n : ℝ)⁻¹ :=
        add_le_add t1 ((norm_sum_le _ _).trans (Finset.sum_le_sum t2))
    _ = |K| * P + |K| * (1 + |t|) * P * ∑ n ∈ Finset.range N, (n : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ |K| * P + |K| * (1 + |t|) * P * (1 + Real.log N) :=
        by have h0 : 0 ≤ |K| * (1 + |t|) * P := by positivity
           linarith [mul_le_mul_of_nonneg_left hharm h0]
    _ = |K| * ((1 + |t|) * (2 + Real.log N)) * P - |K| * P * |t| := by ring
    _ ≤ _ := by linarith

/-- `(1+|t|)² e^{-(t−α)²/(4b)} ≤ (2(1+|α|)² + 16) e^{-(t−α)²/(8b)}` for `0 < b ≤ 1`. -/
lemma poly_gauss_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α t : ℝ) :
    (1 + |t|) ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))
      ≤ (2 * (1 + |α|) ^ 2 + 16) * Real.exp (-(t - α) ^ 2 / (8 * b)) := by
  have h1 : 1 + |t| ≤ (1 + |α|) + |t - α| := by
    have := abs_sub_abs_le_abs_sub t α; linarith
  have h2 : (1 + |t|) ^ 2 ≤ 2 * (1 + |α|) ^ 2 + 2 * (t - α) ^ 2 := by
    have h0 : 0 ≤ 1 + |t| := by positivity
    have := pow_le_pow_left₀ h0 h1 2
    nlinarith [sq_abs (t - α), sq_nonneg ((1 + |α|) - |t - α|)]
  have hg : Real.exp (-(t - α) ^ 2 / (4 * b)) ≤ Real.exp (-(t - α) ^ 2 / (8 * b)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (t - α)]
  have hs := sq_gauss_le hb (t - α)
  have hE0 := Real.exp_pos (-(t - α) ^ 2 / (4 * b))
  have hE8 := Real.exp_pos (-(t - α) ^ 2 / (8 * b))
  have h8 : 8 * b * Real.exp (-(t - α) ^ 2 / (8 * b)) ≤ 8 * Real.exp (-(t - α) ^ 2 / (8 * b)) := by
    nlinarith
  calc (1 + |t|) ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))
      ≤ (2 * (1 + |α|) ^ 2 + 2 * (t - α) ^ 2) * Real.exp (-(t - α) ^ 2 / (4 * b)) :=
        mul_le_mul_of_nonneg_right h2 hE0.le
    _ = 2 * (1 + |α|) ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))
          + 2 * ((t - α) ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))) := by ring
    _ ≤ 2 * (1 + |α|) ^ 2 * Real.exp (-(t - α) ^ 2 / (8 * b))
          + 2 * (8 * Real.exp (-(t - α) ^ 2 / (8 * b))) := by
        linarith [hs.trans h8, mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 2 * (1 + |α|) ^ 2)]
    _ = _ := by ring

/-- **Window bound from a Möbius partial-sum bound** (explicit constant). -/
theorem headWindow_le_of_moebius {K θ' : ℝ} (hθ' : 1 / 2 ≤ θ')
    (hA : ∀ n : ℕ, 1 ≤ n →
      |∑ k ∈ Finset.range (n + 1), (ArithmeticFunction.moebius k : ℝ)| ≤ K * (n : ℝ) ^ θ')
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α : ℝ) :
    headWindow b α ≤ K ^ 2 * (2 + 11 / (10 * b)) ^ 2
      * Real.exp ((11 / 10) * (2 * θ' - 1) / b) * ((2 * (1 + |α|) ^ 2 + 16) * Real.sqrt (8 * π)) := by
  set N := FleetFiniteHeadRH.cut b with hN
  have hN1 : 1 ≤ N := cut_pos hb hb1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNe : (N : ℝ) ≤ Real.exp (11 / (10 * b)) := cut_le
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hL : Real.log N ≤ 11 / (10 * b) := log_cut_le hb hb1
  set P := (N : ℝ) ^ (θ' - 1 / 2) with hP
  have hP0 : 0 ≤ P := by positivity
  have hPle : P ≤ Real.exp (11 / (10 * b) * (θ' - 1 / 2)) := by
    rw [Real.exp_mul]
    exact Real.rpow_le_rpow hNpos.le hNe (by linarith)
  have hP2 : P ^ 2 ≤ Real.exp ((11 / 10) * (2 * θ' - 1) / b) := by
    calc P ^ 2 ≤ Real.exp (11 / (10 * b) * (θ' - 1 / 2)) ^ 2 := pow_le_pow_left₀ hP0 hPle 2
      _ = _ := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp; ring
  set E := Real.exp ((11 / 10) * (2 * θ' - 1) / b)
  set Q := 2 * (1 + |α|) ^ 2 + 16
  have hpt : ∀ t : ℝ, ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))
      ≤ (K ^ 2 * (2 + 11 / (10 * b)) ^ 2 * E * Q) * Real.exp (-(t - α) ^ 2 / (8 * b)) := by
    intro t
    have h := norm_Mpoly_half_le_of_moebius hθ' hA hN1 t
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    have hLL : (2 + Real.log N) ^ 2 ≤ (2 + 11 / (10 * b)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hg := poly_gauss_le hb hb1 α t
    have hE0 := Real.exp_pos (-(t - α) ^ 2 / (4 * b))
    have e : (|K| * ((1 + |t|) * (2 + Real.log N)) * P) ^ 2
        = K ^ 2 * (2 + Real.log N) ^ 2 * P ^ 2 * (1 + |t|) ^ 2 := by rw [← sq_abs K]; ring
    rw [e] at h2
    calc ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))
        ≤ K ^ 2 * (2 + Real.log N) ^ 2 * P ^ 2 * (1 + |t|) ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b)) :=
          mul_le_mul_of_nonneg_right h2 hE0.le
      _ = K ^ 2 * (2 + Real.log N) ^ 2 * P ^ 2 * ((1 + |t|) ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))) := by
          ring
      _ ≤ K ^ 2 * (2 + 11 / (10 * b)) ^ 2 * E * (Q * Real.exp (-(t - α) ^ 2 / (8 * b))) := by
          apply mul_le_mul _ hg (by positivity) (by positivity)
          apply mul_le_mul _ hP2 (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hLL (by positivity)
      _ = _ := by ring
  have hint := integral_mono (integrable_M_window hb N α)
    ((integrable_gauss_scale (d := 8 * b) (by positivity) α).const_mul _) hpt
  rw [integral_const_mul, integral_gauss_scale (by positivity)] at hint
  have hs : Real.sqrt (π * (8 * b)) ≤ Real.sqrt (8 * π) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  unfold headWindow
  calc _ ≤ K ^ 2 * (2 + 11 / (10 * b)) ^ 2 * E * Q * Real.sqrt (π * (8 * b)) := hint
    _ ≤ K ^ 2 * (2 + 11 / (10 * b)) ^ 2 * E * Q * Real.sqrt (8 * π) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- **Converse, Möbius form.** A Möbius partial-sum bound with exponent `θ ≥ 1/2` gives the window rate
`(11/5)(θ − 1/2) + ε` for every `ε > 0` (the constant depends on `α`). -/
theorem windowRate_of_moebiusSumBound {θ : ℝ} (hθ : 1 / 2 ≤ θ) (h : MoebiusSumBound θ)
    {ε : ℝ} (hε : 0 < ε) : WindowRate ((11 / 5) * (θ - 1 / 2) + ε) := by
  intro α _
  obtain ⟨K, hK⟩ := h (ε / 11) (by positivity)
  set θ' := θ + ε / 11
  have hθ' : 1 / 2 ≤ θ' := by simp only [θ']; linarith
  set Q := (2 * (1 + |α|) ^ 2 + 16) * Real.sqrt (8 * π)
  set c₀ := ε / 4
  have hc₀ : 0 < c₀ := by positivity
  refine ⟨K ^ 2 * (4 * (1 + 1 / c₀) ^ 2) * Q, fun b hb hb1 => ?_⟩
  have hw := headWindow_le_of_moebius hθ' hK hb hb1 α
  set u := 1 / b with hu
  have hu0 : 0 ≤ u := by positivity
  have p1 := pow_le_exp 1 hc₀ hu0
  rw [pow_one, Nat.factorial_one, Nat.cast_one, pow_one] at p1
  have hE1 : 1 ≤ Real.exp (c₀ * u) := Real.one_le_exp (by positivity)
  have h1u : 1 + u ≤ (1 + 1 / c₀) * Real.exp (c₀ * u) := by nlinarith
  have h2 : (2 + 11 / (10 * b)) ^ 2 ≤ 4 * (1 + 1 / c₀) ^ 2 * Real.exp ((ε / 2) * u) := by
    have a : 2 + 11 / (10 * b) ≤ 2 * (1 + u) := by
      rw [hu]
      have : 11 / (10 * b) ≤ 2 * (1 / b) := by
        rw [div_le_iff₀ (by positivity)]; field_simp; linarith
      linarith
    have b2 : 2 * (1 + u) ≤ 2 * ((1 + 1 / c₀) * Real.exp (c₀ * u)) := by linarith
    calc (2 + 11 / (10 * b)) ^ 2 ≤ (2 * ((1 + 1 / c₀) * Real.exp (c₀ * u))) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (a.trans b2) 2
      _ = 4 * (1 + 1 / c₀) ^ 2 * (Real.exp (c₀ * u) ^ 2) := by ring
      _ = _ := by rw [← Real.exp_nat_mul]; congr 2; simp only [c₀]; push_cast; ring
  have he : Real.exp ((11 / 10) * (2 * θ' - 1) / b) * Real.exp ((ε / 2) * u)
      ≤ Real.exp (((11 / 5) * (θ - 1 / 2) + ε) / b) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    simp only [θ', hu]
    have : (11 / 10) * (2 * (θ + ε / 11) - 1) / b + ε / 2 * (1 / b)
        = ((11 / 5) * (θ - 1 / 2) + (7 / 10) * ε) / b := by field_simp; ring
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith) hb.le
  have hQ0 : 0 ≤ Q := by positivity
  calc headWindow b α
      ≤ K ^ 2 * (2 + 11 / (10 * b)) ^ 2 * Real.exp ((11 / 10) * (2 * θ' - 1) / b) * Q := hw
    _ ≤ K ^ 2 * (4 * (1 + 1 / c₀) ^ 2 * Real.exp ((ε / 2) * u))
          * Real.exp ((11 / 10) * (2 * θ' - 1) / b) * Q := by gcongr
    _ = K ^ 2 * (4 * (1 + 1 / c₀) ^ 2) * Q
          * (Real.exp ((11 / 10) * (2 * θ' - 1) / b) * Real.exp ((ε / 2) * u)) := by ring
    _ ≤ K ^ 2 * (4 * (1 + 1 / c₀) ^ 2) * Q * Real.exp (((11 / 5) * (θ - 1 / 2) + ε) / b) :=
        mul_le_mul_of_nonneg_left he (by positivity)

/-- The optimal rate is at most `(11/5)(θ − 1/2)` under a Möbius partial-sum bound with exponent `θ`. -/
theorem windowRateInf_le_of_moebiusSumBound {θ : ℝ} (hθ : 1 / 2 ≤ θ) (h : MoebiusSumBound θ) :
    windowRateInf ≤ (11 / 5) * (θ - 1 / 2) :=
  le_of_forall_pos_le_add fun ε hε =>
    windowRateInf_le_of_windowRate (by nlinarith) (windowRate_of_moebiusSumBound hθ h hε)

/-- `Σ_{n≤N} μ(n) ≪ N^{1/2+ε}` gives the subexponential window bound. -/
theorem windowSubexp_of_moebiusSumBound_half (h : MoebiusSumBound (1 / 2)) : WindowSubexpBound := by
  rw [windowSubexp_iff_forall_windowRate]
  intro c hc
  have := windowRate_of_moebiusSumBound (le_refl _) h hc
  simpa using this

/-! ## The converse with the strip as hypothesis -/

/-- The strip of half-width `δ`: every nontrivial zero has `|Re ρ − 1/2| ≤ δ` (equivalently `D ≤ δ`). -/
def StripBound (δ : ℝ) : Prop := ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.re - 1 / 2| ≤ δ

/-- **Landau's transfer at half-width `δ`** (classical, not formalized here): if every nontrivial zero has
`|Re ρ − 1/2| ≤ δ` then `Σ_{n≤N} μ(n) ≪ N^{1/2+δ+ε}` for every `ε > 0`. The case `δ = 0` is
Littlewood's theorem (Titchmarsh, *The Theory of the Riemann Zeta-Function*, §14.25); general `δ` is the same proof.
Carried as a hypothesis. -/
def LandauTransfer (δ : ℝ) : Prop := StripBound δ → MoebiusSumBound (1 / 2 + δ)

/-- **Converse, strip form.** Strip of half-width `δ` ⇒ window rate `(11/5)δ + ε` for every `ε > 0`,
given Landau's transfer at `δ`. -/
theorem windowRate_of_strip {δ : ℝ} (hδ : 0 ≤ δ) (hL : LandauTransfer δ) (hs : StripBound δ)
    {ε : ℝ} (hε : 0 < ε) : WindowRate ((11 / 5) * δ + ε) := by
  have := windowRate_of_moebiusSumBound (by linarith) (hL hs) hε
  simpa using this

theorem windowRateInf_le_of_strip {δ : ℝ} (hδ : 0 ≤ δ) (hL : LandauTransfer δ) (hs : StripBound δ) :
    windowRateInf ≤ (11 / 5) * δ := by
  have := windowRateInf_le_of_moebiusSumBound (by linarith) (hL hs)
  simpa using this

/-- **RH ⟺ the subexponential window bound**, given Littlewood's theorem (`LandauTransfer 0`). -/
theorem RH_iff_windowSubexp (hL : LandauTransfer 0) : RiemannHypothesis ↔ WindowSubexpBound := by
  constructor
  · intro hRH
    have hs : StripBound 0 := fun ρ hρ => by
      rw [riemannHypothesis_iff.mp hRH ρ hρ]; simp
    have := hL hs
    rw [add_zero] at this
    exact windowSubexp_of_moebiusSumBound_half this
  · exact RH_of_window_subexp

/-- The `δ = 3/8` instance under `QuasiRHWiring.QuasiRH` (`ζ(s) ≠ 0` for `Re s > 7/8`, carried as a
hypothesis): the strip `|Re ρ − 1/2| ≤ 3/8` holds. -/
theorem stripBound_of_quasiRH (hQ : QuasiRHWiring.QuasiRH) : StripBound (3 / 8) := fun ρ hρ => by
  have := QuasiRHWiring.abs_half_sub_re_le hQ hρ
  rwa [abs_sub_comm] at this

/-- **The `δ = 3/8` instance**: `QuasiRH` and Landau's transfer at `3/8` give the window rate `33/40 + ε`. -/
theorem windowRate_of_quasiRH (hQ : QuasiRHWiring.QuasiRH) (hL : LandauTransfer (3 / 8))
    {ε : ℝ} (hε : 0 < ε) : WindowRate (33 / 40 + ε) := by
  have := windowRate_of_strip (by norm_num) hL (stripBound_of_quasiRH hQ) hε
  norm_num at this ⊢
  exact this

/-! ## The rate can never beat `D²/2` -/

/-- **No window rate below `D²/2`.** If `W(c)` holds with `c < D²/2` and either `c ≥ 0` or `D > 0`, contradiction.
(The remaining case `D = 0`, `c < 0`, would need a positive lower bound for the window under RH.) -/
theorem not_windowRate_of_lt {c : ℝ} (hc : c < zeroDev ^ 2 / 2) (h' : 0 ≤ c ∨ 0 < zeroDev) :
    ¬ WindowRate c := by
  intro h
  rcases h' with hc0 | hD
  · have h1 := zeroDev_le_of_windowRate hc0 h
    have h2 : zeroDev ^ 2 ≤ 2 * c := by
      calc zeroDev ^ 2 ≤ Real.sqrt (2 * c) ^ 2 := pow_le_pow_left₀ zeroDev_nonneg h1 2
        _ = 2 * c := Real.sq_sqrt (by positivity)
    linarith
  · by_cases hc0 : 0 ≤ c
    · have h1 := zeroDev_le_of_windowRate hc0 h
      have h2 : zeroDev ^ 2 ≤ 2 * c := by
        calc zeroDev ^ 2 ≤ Real.sqrt (2 * c) ^ 2 := pow_le_pow_left₀ zeroDev_nonneg h1 2
          _ = 2 * c := Real.sq_sqrt (by positivity)
      linarith
    · push Not at hc0
      have h0 := zeroDev_le_of_windowRate le_rfl (windowRate_mono hc0.le h)
      simp at h0
      linarith

/-- The `η`-form: for `0 < η ≤ D²/2` the rate `D²/2 − η` is impossible. -/
theorem not_windowRate_sub {η : ℝ} (hη : 0 < η) (hηD : η ≤ zeroDev ^ 2 / 2) :
    ¬ WindowRate (zeroDev ^ 2 / 2 - η) :=
  not_windowRate_of_lt (by linarith) (Or.inl (by linarith))

/-- **The optimal rate, bracketed.** `D²/2 ≤ c* ≤ 11/10`, and `c* ≤ (11/5) D` given Landau's transfer at `D`. -/
theorem windowRateInf_bounds (hL : LandauTransfer zeroDev) :
    zeroDev ^ 2 / 2 ≤ windowRateInf ∧ windowRateInf ≤ 11 / 10 ∧ windowRateInf ≤ (11 / 5) * zeroDev :=
  ⟨zeroDev_sq_half_le_windowRateInf, windowRateInf_le_eleven_tenths,
    windowRateInf_le_of_strip zeroDev_nonneg hL fun _ hρ => le_zeroDev hρ⟩

end FleetHeadContour
