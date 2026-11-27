import FleetHeatPositivityRH
import FleetHeatMonotone
import ZetaConj
import FleetLowZeroFree

/-!
# `R_b(q) > 0` for all `q` when `0.075 ≤ b ≤ 1`: Theorem 2 and the composition

`research_notes/DUAL-INEQUALITY/POSITIVITY_CERTIFIED.md`. `R_b(q) = rhs(gauss b q)`, equal to the zero
trace `Σ_ρ √(π/b) e^{-(t_ρ−q)²/(4b)}` (`FleetPrimePoleBoundRH.zero_trace_eq_rhs`).

External inputs are named hypotheses (none is an axiom):
* `PlattTrudgian` — Platt & Trudgian, *The Riemann hypothesis is true up to 3·10¹²*,
  Bull. LMS 53 (2021): every nontrivial zero with `0 < Im ρ ≤ 3·10¹²` has `Re ρ = ½`.
* `TrudgianNT` — Trudgian, *An improved upper bound for the argument of the Riemann zeta-function on
  the critical line II*, J. Number Theory 134 (2014), Corollary 1 with `T₀ = T`:
  `|N(T) − (T/2π) log(T/2πe) − 7/8| ≤ 0.112 log T + 0.278 log log T + 2.51 + 0.2/T` for `T ≥ e`,
  `N(T)` the number of zeros with imaginary part in `(0, T)`, counted with multiplicity.
  (Constants as cited in the repo's Tier C table; arXiv:1208.5846v2 states the smaller
  `0.111, 0.275, 2.450`, which implies this form.)
* `Certificate075` — Theorem 1 of the note, the Tier B interval-arithmetic certificate
  `tools/certify_positivity_b075.py`: `R_b(q) > 0` for `|q| ≥ 7.516·10¹¹`, `b ∈ [0.075, 1]`.

Proved here:
* `theorem2`: `PlattTrudgian → TrudgianNT → ∀ b ∈ (0,1], ∀ |q| ≤ 3·10¹² − 40, 0 < Re R_b(q)`.
  Route: a verified zero within `16.5` of `q` (for `|q| ≥ 150`, from the count over `[q−16.5, q+16.5)`)
  or within `350` (for `|q| < 150`, a zero in `[e, 200)`); zeros off the line have `|γ| > 3·10¹²`,
  hence distance `≥ D = 3·10¹² − |q| ≥ 40`; their total is bounded by the unconditional band count
  `Σ_{|Im ρ − T| ≤ 1} ord ρ ≤ 300 log |T|` (`ZeroSumLimit.sum_zetaOrder_near_height_le`).
  The note's `[14, 1000]` step used tabulated zeros; here that range is covered by Trudgian's bound.
* `composite`: the three hypotheses give `0 < Re R_b(q)` for all real `q`, `0.075 ≤ b ≤ 1`;
  `composite_all_large_b`: with heat monotonicity, `0 ≤ Re R_b(q)` for all `b ≥ 0.075`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set
open scoped Real ComplexConjugate
open OffLineDetection ZeroSumLimit Reduction GaussianTest

namespace FleetPositivityComposite

/-- The verification height `H = 3·10¹²`. -/
def Hgt : ℝ := 3 * 10 ^ 12

/-- **Platt–Trudgian 2021.** -/
def PlattTrudgian : Prop :=
  ∀ ρ : ℂ, IsNontrivialZero ρ → 0 < ρ.im → ρ.im ≤ 3 * 10 ^ 12 → ρ.re = 1 / 2

/-- `N(T)`: zeros with imaginary part in `(0, T)`, with multiplicity (indices of the canonical
enumeration). -/
def zeroCount (T : ℝ) : ℕ := Nat.card {x : Index | 0 < (t x).re ∧ (t x).re < T}

/-- Error term of Trudgian's corollary. -/
def errT (T : ℝ) : ℝ := 0.112 * Real.log T + 0.278 * Real.log (Real.log T) + 2.51 + 0.2 / T

/-- Main term `(T/2π) log(T/2πe)`. -/
def mainT (T : ℝ) : ℝ := T / (2 * π) * Real.log (T / (2 * π * Real.exp 1))

/-- **Trudgian 2014, Corollary 1** (with `T₀ = T`). -/
def TrudgianNT : Prop :=
  ∀ T : ℝ, Real.exp 1 ≤ T → |(zeroCount T : ℝ) - mainT T - 7 / 8| ≤ errT T

/-- **Theorem 1 of the note** (Tier B certificate `tools/certify_positivity_b075.py`). -/
def Certificate075 : Prop :=
  ∀ b : ℝ, 0.075 ≤ b → b ≤ 1 → ∀ q : ℝ, 7516 * 10 ^ 8 ≤ |q| →
    0 < (FleetFullLineArithmetic.rhs (gauss b q)).re

/-! ## Numerical facts -/

lemma e_gt : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
lemma e_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9

lemma exp_nat_ge (n : ℕ) : (2.7 : ℝ) ^ n ≤ Real.exp n := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) e_gt.le n

lemma exp3_lt : Real.exp 3 < 20.09 := by
  have h : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [Real.exp_one_pow]; norm_num
  rw [h]
  calc Real.exp 1 ^ 3 < 2.7182818286 ^ 3 := pow_lt_pow_left₀ e_lt (Real.exp_pos 1).le (by norm_num)
    _ < 20.09 := by norm_num

lemma two_pi_e3_lt : 2 * π * Real.exp 3 < 126.6 := by
  have := Real.pi_lt_d2
  have h3 := exp3_lt
  have hp := Real.pi_pos
  nlinarith [Real.exp_pos 3]

lemma H_le_exp29 : Hgt + 20 ≤ Real.exp 29 := by
  have := exp_nat_ge 29
  push_cast at this
  unfold Hgt
  linarith [show (3 * 10 ^ 12 + 20 : ℝ) ≤ 2.7 ^ 29 by norm_num]

lemma log29_le : Real.log 29 ≤ 4 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := exp_nat_ge 4
  push_cast at this
  linarith [show (29 : ℝ) ≤ 2.7 ^ 4 by norm_num]

lemma log200_le : Real.log 200 ≤ 6 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := exp_nat_ge 6
  push_cast at this
  linarith [show (200 : ℝ) ≤ 2.7 ^ 6 by norm_num]

lemma log6_le : Real.log 6 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := exp_nat_ge 2
  push_cast at this
  linarith [show (6 : ℝ) ≤ 2.7 ^ 2 by norm_num]

lemma big_lt_exp40 : 1200 * (Hgt + 2) < Real.exp 40 := by
  have := exp_nat_ge 40
  push_cast at this
  unfold Hgt
  linarith [show (1200 * (3 * 10 ^ 12 + 2) : ℝ) < 2.7 ^ 40 by norm_num]

/-! ## Platt–Trudgian on both sides of the real axis -/

lemma ordinate_real_of_PT (hPT : PlattTrudgian) (x : Index) (hx : |(t x).re| ≤ Hgt) :
    (t x).im = 0 := by
  have hρ := multEnum_canonical.nontrivial x
  have hstrip := ZetaStrip.mem_strip_of_isNontrivialZero hρ
  rw [t_im]
  rw [t_re] at hx
  set ρ := canonical x
  rcases lt_trichotomy ρ.im 0 with h | h | h
  · have hc := ZetaConj.isNontrivialZero_conj hρ
    have := hPT (conj ρ) hc (by simp; linarith) (by
      simp only [Complex.conj_im]; unfold Hgt at hx; linarith [neg_abs_le ρ.im])
    simp at this; linarith
  · exfalso
    exact FleetLowZeroFree.zeta_ne_zero_low hstrip.1 hstrip.2 (by rw [h]; norm_num) hρ.1
  · have := hPT ρ hρ h (by unfold Hgt at hx; linarith [le_abs_self ρ.im])
    linarith

/-- The conjugate index: ordinate `−γ`, same imaginary part. -/
lemma exists_conj_index (x : Index) : ∃ x' : Index, (t x').re = -(t x).re ∧ (t x').im = (t x).im := by
  obtain ⟨x', hx'⟩ := multEnum_canonical.exists_index
    (ZetaConj.isNontrivialZero_conj (multEnum_canonical.nontrivial x))
  refine ⟨x', ?_, ?_⟩
  · rw [t_re, t_re, hx']; simp
  · rw [t_im, t_im, hx']; simp

/-! ## Unconditional band count -/

lemma card_le_of_window (s : Finset Index) (T : ℝ) (hT : 4 ≤ |T|)
    (hs : ∀ x ∈ s, |(t x).re - T| ≤ 1) : (s.card : ℝ) ≤ 300 * Real.log |T| := by
  classical
  have hcard : s.card = ∑ ρ ∈ s.image canonical, (s.filter fun x => canonical x = ρ).card :=
    Finset.card_eq_sum_card_image canonical s
  have hle : ∀ ρ ∈ s.image canonical, ((s.filter fun x => canonical x = ρ).card : ℝ) ≤ PrincipalPartDischarge.zetaOrder ρ := by
    intro ρ hρ
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hρ
    exact_mod_cast multEnum_canonical.card_filter_le s (multEnum_canonical.nontrivial x)
  have hsum := sum_zetaOrder_near_height_le T hT (s.image canonical) (by
    intro ρ hρ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hρ
    refine ⟨multEnum_canonical.nontrivial x, ?_⟩
    have := hs x hx
    rwa [t_re] at this)
  calc (s.card : ℝ) = ∑ ρ ∈ s.image canonical, ((s.filter fun x => canonical x = ρ).card : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ ≤ ∑ ρ ∈ s.image canonical, (PrincipalPartDischarge.zetaOrder ρ : ℝ) := Finset.sum_le_sum hle
    _ ≤ _ := hsum

/-- The off-line weight. -/
def farW (b q : ℝ) (x : Index) : ℝ :=
  if (t x).im ≠ 0 then Real.exp (-((t x).re - q) ^ 2 / (4 * b)) else 0

lemma farW_nonneg (b q : ℝ) (x : Index) : 0 ≤ farW b q x := by
  unfold farW; split_ifs <;> positivity

lemma summable_farW {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (q : ℝ) : Summable (farW b q) := by
  refine Summable.of_nonneg_of_le (farW_nonneg b q) (fun x => ?_) (summable_w q)
  unfold farW w
  split_ifs
  · apply Real.exp_le_exp.2
    have h0 : 0 ≤ ((t x).re - q) ^ 2 := sq_nonneg _
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · positivity

/-- **Tail bound for off-line zeros.** If every off-line zero has `|γ| > H ≥ 5` and `|γ − q| ≥ D ≥ 40`,
then `Σ_{off-line} e^{-(γ−q)²/(4b)} ≤ 1200 (|q| + D + 2) e^{-D²/(4b)}` for `0 < b ≤ 1`. -/
theorem tail_le {b q D H : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hD : 40 ≤ D) (hH : 5 ≤ H)
    (hfar : ∀ x : Index, (t x).im ≠ 0 → H < |(t x).re| ∧ D ≤ |(t x).re - q|) :
    ∑' x, farW b q x ≤ 1200 * (|q| + D + 2) * Real.exp (-D ^ 2 / (4 * b)) := by
  classical
  refine (summable_farW hb hb1 q).tsum_le_of_sum_le (fun s => ?_)
  set s' := s.filter (fun x => (t x).im ≠ 0)
  set J : Index → ℕ := fun x => ⌊|(t x).re - q| - D⌋₊
  set A : ℝ := |q| + D + 1
  have hA : 0 ≤ A := by positivity
  have hsum_s : ∑ x ∈ s, farW b q x = ∑ x ∈ s', Real.exp (-((t x).re - q) ^ 2 / (4 * b)) := by
    rw [Finset.sum_filter]; rfl
  -- pointwise bound
  have hpt : ∀ x ∈ s', Real.exp (-((t x).re - q) ^ 2 / (4 * b)) ≤
      Real.exp (-D ^ 2 / (4 * b)) * Real.exp (-20 * (J x : ℝ)) := by
    intro x hx
    have hx' := (hfar x (Finset.mem_filter.1 hx).2).2
    have hJ : (J x : ℝ) ≤ |(t x).re - q| - D := Nat.floor_le (by linarith)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hJ0 : (0 : ℝ) ≤ J x := Nat.cast_nonneg _
    have hsq : (D + J x) ^ 2 ≤ ((t x).re - q) ^ 2 := by
      rw [← sq_abs ((t x).re - q)]
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h4b : 0 < 4 * b := by positivity
    rw [div_add' _ _ _ h4b.ne', div_le_div_iff_of_pos_right h4b]
    nlinarith [mul_le_mul_of_nonneg_left hb1 hJ0]
  -- fiber counts
  have hfib : ∀ j : ℕ, (((s'.filter fun x => J x = j).card : ℕ) : ℝ) ≤ 600 * (A + j) := by
    intro j
    set F := s'.filter fun x => J x = j
    have hmem : ∀ x ∈ F, H < |(t x).re| ∧ D + j ≤ |(t x).re - q| ∧ |(t x).re - q| < D + j + 1 := by
      intro x hx
      have h1 := Finset.mem_filter.1 hx
      have h2 := hfar x (Finset.mem_filter.1 h1.1).2
      have hJ : ⌊|(t x).re - q| - D⌋₊ = j := h1.2
      refine ⟨h2.1, ?_, ?_⟩
      · have := Nat.floor_le (show 0 ≤ |(t x).re - q| - D by linarith [h2.2])
        rw [hJ] at this; linarith
      · have := Nat.lt_floor_add_one (|(t x).re - q| - D)
        rw [hJ] at this; linarith
    have hside : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        (((F.filter fun x => 0 ≤ σ * ((t x).re - q)).card : ℕ) : ℝ) ≤ 300 * (A + j) := by
      intro σ hσ
      set G := F.filter fun x => 0 ≤ σ * ((t x).re - q)
      set T : ℝ := q + σ * (D + j + 1 / 2)
      have hwin : ∀ x ∈ G, |(t x).re - T| ≤ 1 := by
        intro x hx
        have hG := Finset.mem_filter.1 hx
        obtain ⟨-, h1, h2⟩ := hmem x hG.1
        rcases hσ with rfl | rfl
        · have hpos : 0 ≤ (t x).re - q := by linarith [hG.2]
          rw [abs_of_nonneg hpos] at h1 h2
          rw [abs_le]; constructor <;> simp only [T] <;> linarith
        · have hneg : (t x).re - q ≤ 0 := by linarith [hG.2]
          rw [abs_of_nonpos hneg] at h1 h2
          rw [abs_le]; constructor <;> simp only [T] <;> linarith
      rcases G.eq_empty_or_nonempty with hG | ⟨x₀, hx₀⟩
      · rw [hG]; simp; positivity
      · have hT4 : 4 ≤ |T| := by
          have h1 := (hmem x₀ (Finset.mem_filter.1 hx₀).1).1
          have h2 := hwin x₀ hx₀
          have : |(t x₀).re| ≤ |T| + 1 := by
            calc |(t x₀).re| = |((t x₀).re - T) + T| := by ring_nf
              _ ≤ |(t x₀).re - T| + |T| := abs_add_le _ _
              _ ≤ _ := by linarith
          linarith
        have hc := card_le_of_window G T hT4 hwin
        have hTle : |T| ≤ A + j := by
          have : |T| ≤ |q| + |σ| * (D + j + 1 / 2) := by
            simp only [T]
            calc |q + σ * (D + j + 1 / 2)| ≤ |q| + |σ * (D + j + 1 / 2)| := abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < D + j + 1 / 2)]
          have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
          rw [hσ1] at this
          simp only [A]; linarith
        have hlog : Real.log |T| ≤ A + j :=
          (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
        linarith
    have hsplit : F.card = (F.filter fun x => 0 ≤ (1 : ℝ) * ((t x).re - q)).card +
        (F.filter fun x => ¬ 0 ≤ (1 : ℝ) * ((t x).re - q)).card :=
      (Finset.card_filter_add_card_filter_not _).symm
    have hsub : (F.filter fun x => ¬ 0 ≤ (1 : ℝ) * ((t x).re - q)) ⊆
        (F.filter fun x => 0 ≤ (-1 : ℝ) * ((t x).re - q)) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by linarith [not_le.1 hx.2]⟩
    have h1 := hside 1 (Or.inl rfl)
    have h2 := hside (-1) (Or.inr rfl)
    have h3 : (((F.filter fun x => ¬ 0 ≤ (1 : ℝ) * ((t x).re - q)).card : ℕ) : ℝ) ≤
        ((F.filter fun x => 0 ≤ (-1 : ℝ) * ((t x).re - q)).card : ℕ) := by
      exact_mod_cast Finset.card_le_card hsub
    rw [hsplit]; push_cast
    linarith
  -- assemble
  have hgeo : ∀ j : ℕ, 600 * (A + j) * Real.exp (-20 * (j : ℝ)) ≤ 600 * (A + 1) * (1 / 2) ^ j := by
    intro j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : A + j ≤ (A + 1) * (1 + j) := by nlinarith [mul_nonneg hA hj0]
    have h2 : (1 + (j : ℝ)) * Real.exp (-20 * (j : ℝ)) ≤ (1 / 2) ^ j := by
      have hpow : (1 + (j : ℝ)) ≤ 2 ^ j := by
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) j
        norm_num at this; linarith
      have he : (4 : ℝ) ^ j ≤ Real.exp (20 * (j : ℝ)) := by
        rw [show Real.exp (20 * (j : ℝ)) = Real.exp 20 ^ j by rw [← Real.exp_nat_mul]; ring_nf]
        refine pow_le_pow_left₀ (by norm_num) ?_ j
        have := exp_nat_ge 20; push_cast at this
        linarith [show (4 : ℝ) ≤ 2.7 ^ 20 by norm_num]
      have hm : Real.exp (-20 * (j : ℝ)) * Real.exp (20 * (j : ℝ)) = 1 := by
        rw [← Real.exp_add]; simp
      have hpos := Real.exp_pos (-20 * (j : ℝ))
      have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
      have h12 : (1 / 2 : ℝ) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
      have h2pos : (0 : ℝ) < 2 ^ j := by positivity
      -- (1+j) e^{-20j} ≤ 2^j e^{-20j} ≤ 2^j / 4^j = (1/2)^j
      have hA1 : (1 + (j : ℝ)) * Real.exp (-20 * (j : ℝ)) ≤ 2 ^ j * Real.exp (-20 * (j : ℝ)) :=
        mul_le_mul_of_nonneg_right hpow hpos.le
      have hA2 : 2 ^ j * Real.exp (-20 * (j : ℝ)) * (4 : ℝ) ^ j ≤ 2 ^ j := by
        calc 2 ^ j * Real.exp (-20 * (j : ℝ)) * (4 : ℝ) ^ j
            ≤ 2 ^ j * Real.exp (-20 * (j : ℝ)) * Real.exp (20 * (j : ℝ)) :=
              mul_le_mul_of_nonneg_left he (by positivity)
          _ = 2 ^ j := by rw [mul_assoc, hm, mul_one]
      have hA3 : 2 ^ j * Real.exp (-20 * (j : ℝ)) ≤ (1 / 2) ^ j := by
        rw [h4] at hA2
        have : 2 ^ j * Real.exp (-20 * (j : ℝ)) * 2 ^ j ≤ 1 := by
          have := hA2
          have h2' : 2 ^ j * Real.exp (-20 * (j : ℝ)) * (2 ^ j * 2 ^ j) =
              (2 ^ j * Real.exp (-20 * (j : ℝ)) * 2 ^ j) * 2 ^ j := by ring
          rw [h2'] at this
          exact le_of_mul_le_mul_right (by linarith) h2pos
        calc 2 ^ j * Real.exp (-20 * (j : ℝ)) = 2 ^ j * Real.exp (-20 * (j : ℝ)) * 2 ^ j * (1 / 2) ^ j := by
              rw [mul_assoc _ (2 ^ j), mul_comm (2 ^ j : ℝ) ((1/2) ^ j), h12, mul_one]
          _ ≤ 1 * (1 / 2) ^ j := mul_le_mul_of_nonneg_right this (by positivity)
          _ = _ := one_mul _
      linarith
    have h600 : 0 ≤ 600 * (A + 1) := by positivity
    calc 600 * (A + j) * Real.exp (-20 * (j : ℝ)) ≤ 600 * ((A + 1) * (1 + j)) * Real.exp (-20 * (j : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; linarith
      _ = 600 * (A + 1) * ((1 + j) * Real.exp (-20 * (j : ℝ))) := by ring
      _ ≤ 600 * (A + 1) * (1 / 2) ^ j := mul_le_mul_of_nonneg_left h2 h600
  have hgeosum : ∀ u : Finset ℕ, ∑ j ∈ u, ((1 : ℝ) / 2) ^ j ≤ 2 := by
    intro u
    have := summable_geometric_two.sum_le_tsum u (fun j _ => by positivity)
    rwa [tsum_geometric_two] at this
  rw [hsum_s]
  calc ∑ x ∈ s', Real.exp (-((t x).re - q) ^ 2 / (4 * b))
      ≤ ∑ x ∈ s', Real.exp (-D ^ 2 / (4 * b)) * Real.exp (-20 * (J x : ℝ)) := Finset.sum_le_sum hpt
    _ = Real.exp (-D ^ 2 / (4 * b)) * ∑ j ∈ s'.image J,
          (((s'.filter fun x => J x = j).card : ℕ) : ℝ) * Real.exp (-20 * (j : ℝ)) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comp (fun j : ℕ => Real.exp (-20 * (j : ℝ))) J]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [nsmul_eq_mul]
    _ ≤ Real.exp (-D ^ 2 / (4 * b)) * ∑ j ∈ s'.image J, 600 * (A + 1) * (1 / 2) ^ j := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        refine Finset.sum_le_sum (fun j _ => ?_)
        exact (mul_le_mul_of_nonneg_right (hfib j) (Real.exp_pos _).le).trans (hgeo j)
    _ ≤ Real.exp (-D ^ 2 / (4 * b)) * (600 * (A + 1) * 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hgeosum _) (by positivity)
    _ = 1200 * (|q| + D + 2) * Real.exp (-D ^ 2 / (4 * b)) := by simp only [A]; ring

/-! ## Positivity from one near on-line zero and a small off-line tail -/

theorem pos_of_near {b q d : ℝ} (hb : 0 < b) (x₀ : Index) (h0 : (t x₀).im = 0)
    (hd : |(t x₀).re - q| ≤ d) (hsum : Summable (farW b q))
    (hsmall : Real.exp (1 / (16 * b)) * ∑' x, farW b q x < Real.exp (-d ^ 2 / (4 * b))) :
    0 < (∑' x : Index, gaussHat b q (t x)).re := by
  have hS : Summable (fun x : Index => gaussHat b q (t x)) :=
    (GaussianTraceFormula.gaussian_formula_zeros hb q).summable
  set K : ℝ := Real.sqrt (π / b) * Real.exp (1 / (16 * b))
  have hK : 0 ≤ K := by positivity
  set a : Index → ℝ := fun x => (gaussHat b q (t x)).re
  set ℓ : Index → ℝ := fun x => -(K * farW b q x)
  have hre : (∑' x : Index, gaussHat b q (t x)).re = ∑' x, a x := Complex.re_tsum hS
  have has : Summable a := (Complex.hasSum_re hS.hasSum).summable
  have hls : Summable ℓ := (hsum.mul_left K).neg
  have hreal : ∀ x, (t x).im = 0 → a x = Real.sqrt (π / b) * Real.exp (-((t x).re - q) ^ 2 / (4 * b)) := by
    intro x hx
    have ht : t x = ((t x).re : ℂ) := Complex.ext (by simp) (by simp [hx])
    simp only [a]
    rw [ht, gaussHat_eq hb]
    rw [show -(((t x).re : ℂ) - (q : ℂ)) ^ 2 / (4 * (b : ℂ)) =
      ((-((t x).re - q) ^ 2 / (4 * b) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    simp
  have hlow : ∀ x, ℓ x ≤ a x := by
    intro x
    by_cases hx : (t x).im = 0
    · simp only [ℓ, farW, hx, ne_eq, not_true_eq_false, if_false, mul_zero, neg_zero]
      rw [hreal x hx]; positivity
    · simp only [ℓ, farW, hx, ne_eq, not_false_eq_true, if_true]
      have h1 : -‖gaussHat b q (t x)‖ ≤ a x := by
        have := Complex.abs_re_le_norm (gaussHat b q (t x))
        simp only [a]; linarith [neg_abs_le (gaussHat b q (t x)).re]
      refine le_trans ?_ h1
      rw [norm_gaussHat hb, neg_le_neg_iff]
      simp only [K, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have him := t_im_sq_lt x
      have h4b : 0 < 4 * b := by positivity
      rw [show 1 / (16 * b) + -((t x).re - q) ^ 2 / (4 * b) = (1 / 4 - ((t x).re - q) ^ 2) / (4 * b) by
        field_simp; ring]
      rw [div_le_div_iff_of_pos_right h4b]; linarith
  -- Σ a − Σ ℓ ≥ (a − ℓ) x₀
  have hdiff : Summable (fun x => a x - ℓ x) := has.sub hls
  have hx0 : a x₀ - ℓ x₀ ≤ ∑' x, (a x - ℓ x) :=
    hdiff.le_tsum x₀ (fun j _ => sub_nonneg.2 (hlow j))
  rw [has.tsum_sub hls] at hx0
  have hℓx0 : ℓ x₀ = 0 := by simp [ℓ, farW, h0]
  have hax0 : Real.sqrt (π / b) * Real.exp (-d ^ 2 / (4 * b)) ≤ a x₀ := by
    rw [hreal x₀ h0]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply Real.exp_le_exp.2
    have h4b : 0 < 4 * b := by positivity
    rw [div_le_div_iff_of_pos_right h4b, neg_le_neg_iff, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hℓsum : ∑' x, ℓ x = -(K * ∑' x, farW b q x) := by
    simp only [ℓ]; rw [tsum_neg, tsum_mul_left]
  rw [hre]
  have hsq : 0 < Real.sqrt (π / b) := Real.sqrt_pos.2 (by positivity)
  have : Real.sqrt (π / b) * (Real.exp (1 / (16 * b)) * ∑' x, farW b q x) <
      Real.sqrt (π / b) * Real.exp (-d ^ 2 / (4 * b)) := mul_lt_mul_of_pos_left hsmall hsq
  simp only [K] at hℓsum
  linarith

/-! ## Zeros from Trudgian's count -/

lemma mainT_diff {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    (c - a) / (2 * π) * Real.log (a / (2 * π)) ≤ mainT c - mainT a := by
  have hc : 0 < c := lt_of_lt_of_le ha hac
  have hpi : 0 < 2 * π := by positivity
  have hlog : ∀ T : ℝ, 0 < T → Real.log (T / (2 * π * Real.exp 1)) = Real.log T - Real.log (2 * π) - 1 := by
    intro T hT
    rw [Real.log_div hT.ne' (by positivity), Real.log_mul hpi.ne' (Real.exp_pos 1).ne', Real.log_exp]
    ring
  unfold mainT
  rw [hlog c hc, hlog a ha, Real.log_div ha.ne' hpi.ne']
  have key : c - a + (c - a) * Real.log a ≤ c * Real.log c - a * Real.log a := by
    have h1 : 1 - a / c ≤ Real.log (c / a) := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos hc ha)
      rwa [inv_div] at this
    rw [Real.log_div hc.ne' ha.ne'] at h1
    have h2 : c * (1 - a / c) = c - a := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div,
    div_le_div_iff_of_pos_right hpi]
  nlinarith

lemma finite_below (T : ℝ) : {x : Index | 0 < (t x).re ∧ (t x).re < T}.Finite := by
  refine (multEnum_canonical.finite T).subset (fun x hx => ?_)
  simp only [mem_setOf_eq] at hx ⊢
  rw [← t_re, abs_of_pos hx.1]; exact hx.2.le

lemma exists_zero_between (hN : TrudgianNT) {a c : ℝ} (ha : Real.exp 1 ≤ a) (hac : a ≤ c)
    (hgap : errT a + errT c < mainT c - mainT a) :
    ∃ x : Index, a ≤ (t x).re ∧ (t x).re < c := by
  by_contra hno
  push Not at hno
  have hsub : {x : Index | 0 < (t x).re ∧ (t x).re < c} ⊆ {x : Index | 0 < (t x).re ∧ (t x).re < a} := by
    intro x hx
    exact ⟨hx.1, by by_contra h; push Not at h; exact absurd hx.2 (not_lt.2 (hno x h))⟩
  have hle : zeroCount c ≤ zeroCount a := Nat.card_mono (finite_below a) hsub
  have h1 := (abs_le.1 (hN c (ha.trans hac))).1
  have h2 := (abs_le.1 (hN a ha)).2
  have : (zeroCount c : ℝ) ≤ zeroCount a := by exact_mod_cast hle
  linarith

lemma errT_le {T : ℝ} (h1 : Real.exp 1 ≤ T) (h2 : T ≤ Real.exp 29) :
    errT T ≤ 0.112 * 29 + 0.278 * 4 + 2.51 + 0.2 / T := by
  have hT : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) h1
  have hl1 : 1 ≤ Real.log T := by rw [Real.le_log_iff_exp_le hT]; exact h1
  have hl2 : Real.log T ≤ 29 := by rw [Real.log_le_iff_le_exp hT]; exact h2
  have hll : Real.log (Real.log T) ≤ 4 :=
    (Real.log_le_log (by linarith) hl2).trans log29_le
  unfold errT; linarith

/-- For `150 ≤ q ≤ H − 40`, an on-line zero within `16.5` of `q`. -/
lemma near_zero_large (hPT : PlattTrudgian) (hN : TrudgianNT) {q : ℝ} (hq1 : 150 ≤ q)
    (hq2 : q ≤ Hgt - 40) : ∃ x : Index, (t x).im = 0 ∧ |(t x).re - q| ≤ 16.5 := by
  have he := e_lt
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have ha : Real.exp 1 ≤ q - 16.5 := by linarith
  have hc29 : q + 16.5 ≤ Real.exp 29 := by have := H_le_exp29; linarith
  have hlog : 3 ≤ Real.log ((q - 16.5) / (2 * π)) := by
    rw [Real.le_log_iff_exp_le (div_pos (by linarith) (by positivity)), le_div_iff₀ (by positivity)]
    have := two_pi_e3_lt; nlinarith
  have hmain := mainT_diff (show 0 < q - 16.5 by linarith) (show q - 16.5 ≤ q + 16.5 by linarith)
  have hE1 := errT_le ha (by linarith)
  have hE2 := errT_le (show Real.exp 1 ≤ q + 16.5 by linarith) hc29
  have hinv1 : 0.2 / (q - 16.5) ≤ 0.002 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hinv2 : 0.2 / (q + 16.5) ≤ 0.002 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hlow : 15.7 ≤ (q + 16.5 - (q - 16.5)) / (2 * π) * Real.log ((q - 16.5) / (2 * π)) := by
    rw [show q + 16.5 - (q - 16.5) = (33 : ℝ) by ring]
    have h33 : 33 / (2 * π) ≥ 33 / 6.3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity); linarith
    have : (33 : ℝ) / 6.3 * 3 ≥ 15.7 := by norm_num
    nlinarith [div_pos (show (0:ℝ) < 33 by norm_num) (show (0:ℝ) < 2 * π by positivity)]
  obtain ⟨x, hx1, hx2⟩ := exists_zero_between (c := q + 16.5) hN ha (by linarith) (by linarith)
  refine ⟨x, ordinate_real_of_PT hPT x ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith [Real.exp_pos 1]
  · rw [abs_le]; constructor <;> linarith

/-- An on-line zero with ordinate in `[e, 200)`. -/
lemma low_zero (hPT : PlattTrudgian) (hN : TrudgianNT) :
    ∃ x : Index, (t x).im = 0 ∧ Real.exp 1 ≤ (t x).re ∧ (t x).re < 200 := by
  have he := e_lt
  have he' := e_gt
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hc : Real.exp 1 ≤ 200 := by linarith
  have h200 : Real.exp 1 ≤ Real.exp 29 := Real.exp_le_exp.2 (by norm_num)
  -- main term at 200 is at least 63; at e it is ≤ 0
  have hm200 : 63 ≤ mainT 200 := by
    unfold mainT
    have hl : 2 ≤ Real.log (200 / (2 * π * Real.exp 1)) := by
      rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity),
        show Real.exp 2 * (2 * π * Real.exp 1) = 2 * π * Real.exp 3 by
          rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.exp_add]; ring]
      linarith [two_pi_e3_lt]
    have h1 : (200 : ℝ) / (2 * π) ≥ 200 / 6.3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity); linarith
    have : (200 : ℝ) / 6.3 * 2 ≥ 63 := by norm_num
    nlinarith [div_pos (show (0:ℝ) < 200 by norm_num) (show (0:ℝ) < 2 * π by positivity)]
  have hme : mainT (Real.exp 1) ≤ 0 := by
    unfold mainT
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    apply Real.log_nonpos (by positivity)
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    nlinarith [Real.exp_pos 1]
  have hE200 : errT 200 ≤ 3.8 := by
    unfold errT
    have hl : Real.log 200 ≤ 6 := log200_le
    have hl0 : 0 < Real.log 200 := Real.log_pos (by norm_num)
    have hll : Real.log (Real.log 200) ≤ 2 := (Real.log_le_log hl0 hl).trans log6_le
    norm_num at hll ⊢; nlinarith
  have hEe : errT (Real.exp 1) ≤ 2.75 := by
    unfold errT
    rw [Real.log_exp, Real.log_one]
    have : 0.2 / Real.exp 1 ≤ 0.08 := by rw [div_le_iff₀ (Real.exp_pos 1)]; linarith
    linarith
  obtain ⟨x, hx1, hx2⟩ := exists_zero_between (c := 200) hN le_rfl hc (by linarith)
  refine ⟨x, ordinate_real_of_PT hPT x ?_, hx1, hx2⟩
  unfold Hgt
  rw [abs_le]; constructor <;> linarith [Real.exp_pos 1]

/-! ## Theorem 2 -/

/-- **Theorem 2** (given Platt–Trudgian and Trudgian's count): `Re R_b(q) > 0` for every
`b ∈ (0, 1]` and `|q| ≤ 3·10¹² − 40`. -/
theorem theorem2 (hPT : PlattTrudgian) (hN : TrudgianNT) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    {q : ℝ} (hq : |q| ≤ Hgt - 40) : 0 < (FleetFullLineArithmetic.rhs (gauss b q)).re := by
  rw [← FleetPrimePoleBoundRH.zero_trace_eq_rhs hb q]
  change 0 < (∑' x : Index, gaussHat b q (t x)).re
  have hH : (5 : ℝ) ≤ Hgt := by unfold Hgt; norm_num
  set D : ℝ := Hgt - |q| with hDdef
  have hD40 : 40 ≤ D := by rw [hDdef]; linarith
  have hfar : ∀ x : Index, (t x).im ≠ 0 → Hgt < |(t x).re| ∧ D ≤ |(t x).re - q| := by
    intro x hx
    have h1 : Hgt < |(t x).re| := by
      by_contra h; push Not at h; exact hx (ordinate_real_of_PT hPT x h)
    refine ⟨h1, ?_⟩
    have := abs_sub_abs_le_abs_sub (t x).re q
    rw [hDdef]; linarith
  -- choose the near zero and its distance
  obtain ⟨x₀, h0, d, hd, hdD⟩ : ∃ x₀ : Index, (t x₀).im = 0 ∧ ∃ d : ℝ,
      |(t x₀).re - q| ≤ d ∧ 160 ≤ D ^ 2 - d ^ 2 - 1 / 4 := by
    by_cases hbig : 150 ≤ |q|
    · rcases le_or_gt 0 q with hq0 | hq0
      · rw [abs_of_nonneg hq0] at hbig hq
        obtain ⟨x, hx, hxd⟩ := near_zero_large hPT hN hbig hq
        refine ⟨x, hx, 16.5, hxd, ?_⟩
        nlinarith
      · rw [abs_of_neg hq0] at hbig hq
        obtain ⟨x, hx, hxd⟩ := near_zero_large hPT hN hbig hq
        obtain ⟨x', hre, him⟩ := exists_conj_index x
        refine ⟨x', by rw [him]; exact hx, 16.5, ?_, ?_⟩
        · rw [hre, show -(t x).re - q = -((t x).re - -q) by ring, abs_neg]; exact hxd
        · nlinarith
    · push Not at hbig
      obtain ⟨x, hx, hx1, hx2⟩ := low_zero hPT hN
      refine ⟨x, hx, 350, ?_, ?_⟩
      · have := e_gt
        rw [abs_le]; constructor <;> linarith [abs_lt.1 hbig]
      · have hD : 1000 ≤ D := by rw [hDdef]; unfold Hgt; linarith
        nlinarith
  have htail := tail_le hb hb1 hD40 hH hfar
  have hsum := summable_farW hb hb1 q
  refine pos_of_near hb x₀ h0 hd hsum ?_
  have hqD : |q| + D = Hgt := by rw [hDdef]; ring
  rw [hqD] at htail
  have h4b : 0 < 4 * b := by positivity
  -- 1200 (H+2) e^{1/16b} e^{-D²/4b} < e^{-d²/4b}
  have hexp : 1200 * (Hgt + 2) < Real.exp ((D ^ 2 - d ^ 2 - 1 / 4) / (4 * b)) := by
    refine big_lt_exp40.trans_le (Real.exp_le_exp.2 ?_)
    rw [le_div_iff₀ h4b]; nlinarith
  calc Real.exp (1 / (16 * b)) * ∑' x, farW b q x
      ≤ Real.exp (1 / (16 * b)) * (1200 * (Hgt + 2) * Real.exp (-D ^ 2 / (4 * b))) :=
        mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
    _ = 1200 * (Hgt + 2) * Real.exp (-((D ^ 2 - d ^ 2 - 1 / 4) / (4 * b))) *
          Real.exp (-d ^ 2 / (4 * b)) := by
        have e1 : Real.exp (1 / (16 * b)) * Real.exp (-D ^ 2 / (4 * b)) =
            Real.exp (-((D ^ 2 - d ^ 2 - 1 / 4) / (4 * b))) * Real.exp (-d ^ 2 / (4 * b)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
        calc Real.exp (1 / (16 * b)) * (1200 * (Hgt + 2) * Real.exp (-D ^ 2 / (4 * b)))
            = 1200 * (Hgt + 2) * (Real.exp (1 / (16 * b)) * Real.exp (-D ^ 2 / (4 * b))) := by ring
          _ = _ := by rw [e1]; ring
    _ < Real.exp ((D ^ 2 - d ^ 2 - 1 / 4) / (4 * b)) * Real.exp (-((D ^ 2 - d ^ 2 - 1 / 4) / (4 * b))) *
          Real.exp (-d ^ 2 / (4 * b)) := by
        apply mul_lt_mul_of_pos_right _ (Real.exp_pos _)
        exact mul_lt_mul_of_pos_right hexp (Real.exp_pos _)
    _ = Real.exp (-d ^ 2 / (4 * b)) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- **The composite claim**: Theorem 1 (certificate) + Theorem 2 give `Re R_b(q) > 0` for every real
`q` and every `b ∈ [0.075, 1]`. -/
theorem composite (hC : Certificate075) (hPT : PlattTrudgian) (hN : TrudgianNT) {b : ℝ}
    (hb : 0.075 ≤ b) (hb1 : b ≤ 1) (q : ℝ) : 0 < (FleetFullLineArithmetic.rhs (gauss b q)).re := by
  by_cases hq : 7516 * 10 ^ 8 ≤ |q|
  · exact hC b hb hb1 q hq
  · push Not at hq
    exact theorem2 hPT hN (by linarith) hb1 (by unfold Hgt; linarith)

/-- With heat monotonicity (`FleetHeatMonotone`), the composite claim gives `Re R_b ≥ 0` for every
`b ≥ 0.075`, i.e. the heat-positivity threshold is at most `0.075`. -/
theorem composite_all_large_b (hC : Certificate075) (hPT : PlattTrudgian) (hN : TrudgianNT)
    {b : ℝ} (hb : 0.075 ≤ b) : b ∈ FleetHeatMonotone.heatPositiveWidths := by
  have h075 : (0.075 : ℝ) ∈ FleetHeatMonotone.heatPositiveWidths :=
    ⟨by norm_num, fun α => (composite hC hPT hN le_rfl (by norm_num) α).le⟩
  exact FleetHeatMonotone.heatPositiveWidths_upward_closed h075 hb

end FleetPositivityComposite
