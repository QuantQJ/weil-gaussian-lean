import Kerr.Zeta.ClassicalResults
import Kerr.Zeta.Conjugation
import FleetGammaIdentification
import FleetDigammaGrowth
import Reduction
import Mathlib

/-!
# The first nontrivial zero of `ζ`: a zero on the critical line with ordinate in `(14.13, 14.14)`

`exists_zeta_zero_first` : `∃ t, 14.13 < t < 14.14 ∧ ζ(1/2 + t i) = 0`, and
`exists_nontrivialZero_first` : the same zero as a `Reduction.IsNontrivialZero` with `Re ρ = 1/2`.

Method (no numerics assumed; every number is checked by the Lean kernel with `decide +kernel`):

* `Λ(s) = Γ_ℝ(s) ζ(s)` (`completedRiemannZeta`) is real on `Re s = 1/2` (`Λ(1 − s) = Λ(s)` from Mathlib and
  `Λ(s̄) = conj Λ(s)` from kerr-lean `Kerr.ZetaConj.completedRiemannZeta_conj`) and continuous there, so a sign
  change of `t ↦ Λ(1/2 + t i)` on `[14.13, 14.14]` gives a zero (intermediate value theorem).
* `ζ(1/2 + t i)` at `t = 14.13, 14.14`: fourth-order Euler–Maclaurin with 59 terms and boundary point `60`
  (kerr-lean's copy of `ZetaGrowthEM3.zeta_eq_sum_add_tail₄`), the remainder bounded by `tailQ t ≈ 1.1·10⁻⁴`
  (`zeta_sub_main_le`), the main part enclosed by kerr-lean's verified rational disc arithmetic
  (`Disc`, `powDisc7`) with a kernel-checked table of `log 1, …, log 60` (`lcFOK_true`). Result: discs of
  radius `≈ 1.2·10⁻⁴` around `ζ(1/2 + 14.13 i) ≈ 0.000596 − 0.003699 i` and
  `ζ(1/2 + 14.14 i) ≈ −0.000649 + 0.004135 i` (`zetaD_contains`).
* `Γ_ℝ(s) = exp(Eg s)`, `Eg s = −(s/2) log π + log Γ(s/2)` with hp-proof's regularized Euler logarithm
  (`FleetGammaIdentification.exp_regularizedLogGamma`); its derivative is the digamma series, bounded by `55`
  near `1/4 + 7.07 i` (`FleetDigammaGrowth.norm_logDerivative_le`), so `‖Eg(s₁) − Eg(s₂)‖ ≤ 3/10`
  (`Eg_diff_le`, mean value inequality).
* With `P = ζ(s₁) conj ζ(s₂)`: `Λ(s₁)Λ(s₂) = |Γ_ℝ(s₂)|² Re(e^{Eg(s₁)−Eg(s₂)} P)`, and the kernel-checked
  certificate `Re P + (3/5)‖P‖ < 0` (`signOK_true`) gives `Λ(s₁)Λ(s₂) < 0` (`completedZeta_sign_change`).

The Euler–Maclaurin, disc-arithmetic and logarithm-bracket machinery is kerr-lean's (QJ's repo, Apache-2.0),
already vendored in hp-proof as `Kerr/Zeta/ClassicalResults.lean` (namespace `Kerr.File14RHExtra`); it is used
here unchanged.
-/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Real ComplexConjugate

namespace FleetFirstZero
open Kerr.File14RHExtra Kerr.File14RHExtra.Disc

/-- `lcT.getD i 0 ≈ log (i + 1)`, `i < 60`. -/
def lcT : List ℚ :=
  [(0 : ℚ) / 100000000000,
    (69314718056 : ℚ) / 100000000000,
    (109861228867 : ℚ) / 100000000000,
    (138629436112 : ℚ) / 100000000000,
    (160943791243 : ℚ) / 100000000000,
    (179175946923 : ℚ) / 100000000000,
    (194591014906 : ℚ) / 100000000000,
    (207944154168 : ℚ) / 100000000000,
    (219722457734 : ℚ) / 100000000000,
    (230258509299 : ℚ) / 100000000000,
    (239789527280 : ℚ) / 100000000000,
    (248490664979 : ℚ) / 100000000000,
    (256494935746 : ℚ) / 100000000000,
    (263905732962 : ℚ) / 100000000000,
    (270805020110 : ℚ) / 100000000000,
    (277258872224 : ℚ) / 100000000000,
    (283321334406 : ℚ) / 100000000000,
    (289037175790 : ℚ) / 100000000000,
    (294443897917 : ℚ) / 100000000000,
    (299573227355 : ℚ) / 100000000000,
    (304452243772 : ℚ) / 100000000000,
    (309104245336 : ℚ) / 100000000000,
    (313549421593 : ℚ) / 100000000000,
    (317805383035 : ℚ) / 100000000000,
    (321887582487 : ℚ) / 100000000000,
    (325809653802 : ℚ) / 100000000000,
    (329583686600 : ℚ) / 100000000000,
    (333220451018 : ℚ) / 100000000000,
    (336729582999 : ℚ) / 100000000000,
    (340119738166 : ℚ) / 100000000000,
    (343398720449 : ℚ) / 100000000000,
    (346573590280 : ℚ) / 100000000000,
    (349650756147 : ℚ) / 100000000000,
    (352636052462 : ℚ) / 100000000000,
    (355534806149 : ℚ) / 100000000000,
    (358351893846 : ℚ) / 100000000000,
    (361091791264 : ℚ) / 100000000000,
    (363758615973 : ℚ) / 100000000000,
    (366356164613 : ℚ) / 100000000000,
    (368887945411 : ℚ) / 100000000000,
    (371357206670 : ℚ) / 100000000000,
    (373766961828 : ℚ) / 100000000000,
    (376120011569 : ℚ) / 100000000000,
    (378418963392 : ℚ) / 100000000000,
    (380666248977 : ℚ) / 100000000000,
    (382864139649 : ℚ) / 100000000000,
    (385014760171 : ℚ) / 100000000000,
    (387120101091 : ℚ) / 100000000000,
    (389182029811 : ℚ) / 100000000000,
    (391202300543 : ℚ) / 100000000000,
    (393182563272 : ℚ) / 100000000000,
    (395124371858 : ℚ) / 100000000000,
    (397029191355 : ℚ) / 100000000000,
    (398898404656 : ℚ) / 100000000000,
    (400733318523 : ℚ) / 100000000000,
    (402535169074 : ℚ) / 100000000000,
    (404305126783 : ℚ) / 100000000000,
    (406044301055 : ℚ) / 100000000000,
    (407753744391 : ℚ) / 100000000000,
    (409434456222 : ℚ) / 100000000000]

def lcF (i : ℕ) : ℚ := lcT.getD i 0

def lcFOK : Bool := (List.range 60).all fun i => logBracket (i + 1) (lcF i)

set_option maxRecDepth 100000 in
theorem lcFOK_true : lcFOK = true := by decide +kernel


theorem lcF_near {i : ℕ} (hi : i < 60) : |Real.log ((i + 1 : ℕ) : ℝ) - lcF i| ≤ etaL := by
  have h := lcFOK_true
  simp only [lcFOK, List.all_eq_true, List.mem_range] at h
  exact logBracket_sound (Nat.succ_pos i) (h i hi)

/-! ## The approximant with 59 terms and boundary point `60`, on the critical line -/

/-- The point `1/2 + t i`. -/
def sq (t : ℚ) : ℂ := ((1 / 2 : ℚ) : ℂ) + (t : ℂ) * I

lemma sq_re (t : ℚ) : (sq t).re = 1 / 2 := by simp [sq]
lemma sq_im (t : ℚ) : (sq t).im = t := by simp [sq]

/-- Disc for `(i+1)^{-(1/2 + t i)}`. -/
def pwF (t : ℚ) (i : ℕ) : Disc := powDisc7 (lcF i) (1 / 2) t

lemma pwF_contains {t : ℚ} {i : ℕ} (hi : i < 60) (h64 : |-(1 / 2 : ℚ) * lcF i| + |-t * lcF i| ≤ 64)
    (hη : (|(1 / 2 : ℚ)| + |t|) * etaL ≤ 1 / 2) :
    (pwF t i).Contains (npow i (sq t)) := by
  rw [npow_eq]
  exact powDisc7_contains (Nat.succ_pos i) (lcF_near hi) (1 / 2) t h64 hη

def cinvD (t : ℚ) : Disc :=
  Disc.exact ((1 / 2 - 1) / ((1 / 2 - 1) ^ 2 + t ^ 2)) (-t / ((1 / 2 - 1) ^ 2 + t ^ 2))

/-- Disc for the main part `Σ_{n ≤ 59} n^{-s} + 60^{1-s}/(s-1) + 60^{-s}/2 + (s/12) 60^{-s-1}
 − s(s+1)(s+2)/720 · 60^{-s-3}` at `s = 1/2 + t i`. -/
def mainD (t : ℚ) : Disc :=
  add (add (add (add (sumD (pwF t) 59) (smul 60 (round (mul (pwF t 59) (cinvD t)))))
    (smul (1 / 2) (pwF t 59)))
    (smul (1 / 720) (round (mul (Disc.exact (1 / 2) t) (pwF t 59)))))
    (smul (-(1 / 155520000)) (round (mul (mul (mul (Disc.exact (1 / 2) t) (Disc.exact (3 / 2) t))
      (Disc.exact (5 / 2) t)) (pwF t 59))))

/-- Bound for the Euler–Maclaurin remainder at `s = 1/2 + t i`. -/
def tailQ (t : ℚ) : ℚ :=
  (1 / 2 + |t|) * (3 / 2 + |t|) * (5 / 2 + |t|) * (7 / 2 + |t|) / 720 * (1 / 216000) *
    (2 * (1302 / 10000))

/-- The certified disc for `ζ(1/2 + t i)`. -/
def zetaD (t : ℚ) : Disc := (mainD t).enlarge (tailQ t)

/-- Side conditions of the certificate. -/
def zetaOK (t : ℚ) : Bool :=
  decide (0 < t) &&
    ((List.range 60).all fun i => decide (|-(1 / 2 : ℚ) * lcF i| + |-t * lcF i| ≤ 64)) &&
    decide ((|(1 / 2 : ℚ)| + |t|) * etaL ≤ 1 / 2)


lemma sq_ne_one (t : ℚ) : sq t ≠ 1 := by
  intro h; have := congrArg Complex.re h; rw [sq_re] at this; norm_num at this

/-- The main part, as a complex number. -/
lemma main_contains {t : ℚ} (hc : zetaOK t = true) :
    (mainD t).Contains (∑ i ∈ Finset.range 59, npow i (sq t)
      + ((60 : ℚ) : ℂ) * (npow 59 (sq t) * (sq t - 1)⁻¹) + ((1 / 2 : ℚ) : ℂ) * npow 59 (sq t)
      + ((1 / 720 : ℚ) : ℂ) * (sq t * npow 59 (sq t))
      + ((-(1 / 155520000) : ℚ) : ℂ) * ((sq t * (sq t + 1)) * (sq t + 2) * npow 59 (sq t))) := by
  simp only [zetaOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨ht, h64⟩, hη⟩ := hc
  have hp : ∀ i < 60, (pwF t i).Contains (npow i (sq t)) := fun i hi => pwF_contains hi (h64 i hi) hη
  have hs : (Disc.exact (1 / 2) t).Contains (sq t) := by
    have := exact_contains (1 / 2) t; simpa [sq] using this
  have hs1 : (Disc.exact (3 / 2) t).Contains (sq t + 1) := by
    have := exact_contains (3 / 2) t
    convert this using 1; simp only [sq]; push_cast; ring
  have hs2 : (Disc.exact (5 / 2) t).Contains (sq t + 2) := by
    have := exact_contains (5 / 2) t
    convert this using 1; simp only [sq]; push_cast; ring
  have hci : (cinvD t).Contains ((sq t - 1)⁻¹) := by
    have := cinv_contains (1 / 2) t ht
    simpa [sq, cinvD] using this
  unfold mainD
  refine add_contains (add_contains (add_contains (add_contains ?_ ?_) ?_) ?_) ?_
  · exact sumD_contains 59 fun i hi => hp i (by omega)
  · exact smul_contains _ (round_contains (mul_contains (hp 59 (by norm_num)) hci))
  · exact smul_contains _ (hp 59 (by norm_num))
  · exact smul_contains _ (round_contains (mul_contains hs (hp 59 (by norm_num))))
  · exact smul_contains _ (round_contains (mul_contains (mul_contains (mul_contains hs hs1) hs2)
      (hp 59 (by norm_num))))


open Kerr.File14RHExtra.ZetaGrowth Kerr.File14RHExtra.ZetaGrowthEM3 in
/-- `ζ(1/2+ti)` minus the main part is the Euler–Maclaurin remainder, of norm `≤ tailQ t`. -/
theorem zeta_sub_main_le (t : ℚ) :
    ‖riemannZeta (sq t) - (∑ i ∈ Finset.range 59, npow i (sq t)
      + ((60 : ℚ) : ℂ) * (npow 59 (sq t) * (sq t - 1)⁻¹) + ((1 / 2 : ℚ) : ℂ) * npow 59 (sq t)
      + ((1 / 720 : ℚ) : ℂ) * (sq t * npow 59 (sq t))
      + ((-(1 / 155520000) : ℚ) : ℂ) * ((sq t * (sq t + 1)) * (sq t + 2) * npow 59 (sq t)))‖
      ≤ (tailQ t : ℝ) := by
  set s := sq t with hsdef
  have hre : s.re = 1 / 2 := sq_re t
  have him : s.im = t := sq_im t
  have hs1 : s ≠ 1 := sq_ne_one t
  have hz := zeta_eq_sum_add_tail₄ (s := s) (by rw [hre]; norm_num) hs1 59
  have hx0 : ((59 : ℕ) : ℂ) + 1 ≠ 0 := by norm_num
  have e60 : ((59 : ℕ) : ℂ) + 1 = ((60 : ℚ) : ℂ) := by push_cast; norm_num
  have h1 : (((59 : ℕ) : ℂ) + 1) ^ (1 - s) = ((60 : ℚ) : ℂ) * npow 59 s := by
    rw [show (1 : ℂ) - s = 1 + -s by ring, cpow_add _ _ hx0, cpow_one, npow, e60]
  have h2 : (((59 : ℕ) : ℂ) + 1) ^ (-s - 1) = npow 59 s / 60 := by
    rw [cpow_sub _ _ hx0, cpow_one, npow]; push_cast; ring
  have h3 : (((59 : ℕ) : ℂ) + 1) ^ (-s - 3) = npow 59 s / 216000 := by
    rw [cpow_sub _ _ hx0, show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, cpow_natCast, npow]
    push_cast; ring
  have hdiff : riemannZeta s - (∑ i ∈ Finset.range 59, npow i s
      + ((60 : ℚ) : ℂ) * (npow 59 s * (s - 1)⁻¹) + ((1 / 2 : ℚ) : ℂ) * npow 59 s
      + ((1 / 720 : ℚ) : ℂ) * (s * npow 59 s)
      + ((-(1 / 155520000) : ℚ) : ℂ) * ((s * (s + 1)) * (s + 2) * npow 59 s))
      = ∑' n : ℕ, emTerm₄ (n + 59 + 1) s := by
    rw [hz, h1, h2, h3]
    have hsum : ∑ i ∈ Finset.range 59, ((i : ℂ) + 1) ^ (-s) = ∑ i ∈ Finset.range 59, npow i s := rfl
    have h0 : (((59 : ℕ) : ℂ) + 1) ^ (-s) = npow 59 s := rfl
    rw [hsum, h0]
    push_cast; ring
  rw [hdiff]
  have nA : ‖s‖ ≤ 1 / 2 + |(t : ℝ)| := by
    refine (Disc.norm_le_abs_re_add_abs_im _).trans ?_; rw [hre, him]; norm_num
  have nB : ‖s + 1‖ ≤ 3 / 2 + |(t : ℝ)| := by
    have := norm_add_nat_le s 1 (by norm_num); push_cast at this; rw [hre, him] at this
    norm_num at this; linarith
  have nC : ‖s + 2‖ ≤ 5 / 2 + |(t : ℝ)| := by
    have := norm_add_nat_le s 2 (by norm_num); push_cast at this; rw [hre, him] at this
    norm_num at this; linarith
  have nD : ‖s + 3‖ ≤ 7 / 2 + |(t : ℝ)| := by
    have := norm_add_nat_le s 3 (by norm_num); push_cast at this; rw [hre, him] at this
    norm_num at this; linarith
  set P : ℝ := ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 with hP
  have hP0 : 0 ≤ P := by positivity
  have hPle : P ≤ (1 / 2 + |(t : ℝ)|) * (3 / 2 + |(t : ℝ)|) * (5 / 2 + |(t : ℝ)|) *
      (7 / 2 + |(t : ℝ)|) / 720 := by
    have := mul_le_mul (mul_le_mul (mul_le_mul nA nB (norm_nonneg _) (by positivity)) nC
      (norm_nonneg _) (by positivity)) nD (norm_nonneg _) (by positivity)
    exact div_le_div_of_nonneg_right this (by norm_num)
  have hterm : ∀ n : ℕ, ‖emTerm₄ (n + 59 + 1) s‖ ≤
      P * (1 / 216000) * ((n : ℝ) + (59 : ℕ) + 1) ^ (-(3 / 2 : ℝ)) := by
    intro n
    refine (norm_emTerm₄_le (by rw [hre]; norm_num) hs1 (by omega)).trans ?_
    rw [← hP, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hP0
    push_cast
    have hpos : (0 : ℝ) < (n : ℝ) + 59 + 1 := by positivity
    have hsplit : ((n : ℝ) + 59 + 1) ^ (-s.re - 4) =
        ((n : ℝ) + 59 + 1) ^ (-(3 / 2 : ℝ)) * ((n : ℝ) + 59 + 1) ^ (-s.re - 5 / 2) := by
      rw [← Real.rpow_add hpos]; congr 1; ring
    rw [hsplit, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h60le : (60 : ℝ) ≤ (n : ℝ) + 59 + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    rw [hre]
    calc ((n : ℝ) + 59 + 1) ^ (-(1 / 2 : ℝ) - 5 / 2) ≤ (60 : ℝ) ^ (-(1 / 2 : ℝ) - 5 / 2) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) h60le (by norm_num)
      _ = 1 / 216000 := by
          rw [show -(1 / 2 : ℝ) - 5 / 2 = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
            Real.rpow_natCast]; norm_num
  have hsum := (summable_add_rpow 59 (a := -(3 / 2 : ℝ)) (by norm_num)).mul_left (P * (1 / 216000))
  have htail := tsum_of_norm_bounded hsum.hasSum hterm
  refine htail.trans ?_
  rw [tsum_mul_left]
  have hT := tsum_tail_rpow_le (N := 59) (by norm_num)
  have h3 : ((59 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1302 / 10000 :=
    rpow_neg_le_const 59 (by norm_num) le_rfl (by norm_num) (by norm_num)
  have hT' : ∑' m : ℕ, ((m : ℝ) + (59 : ℕ) + 1) ^ (-(3 / 2 : ℝ)) ≤ 2 * (1302 / 10000) := by
    linarith
  have hq : ((tailQ t : ℚ) : ℝ) = (1 / 2 + |(t : ℝ)|) * (3 / 2 + |(t : ℝ)|) * (5 / 2 + |(t : ℝ)|) *
      (7 / 2 + |(t : ℝ)|) / 720 * (1 / 216000) * (2 * (1302 / 10000)) := by
    simp only [tailQ]; push_cast; ring
  rw [hq]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hPle (by norm_num)) hT'
    (tsum_nonneg fun _ => by positivity) (by positivity)

/-- **`ζ(1/2 + t i)` lies in the certified disc** (whenever the side conditions hold). -/
theorem zetaD_contains {t : ℚ} (hc : zetaOK t = true) : (zetaD t).Contains (riemannZeta (sq t)) :=
  enlarge_contains' _ (main_contains hc) (zeta_sub_main_le t)


/-! ## The archimedean factor `Γ_ℝ(s) = π^{-s/2} Γ(s/2)` as an exponential -/

/-- `log Γ_ℝ(s) = −(s/2) log π + log Γ(s/2)`, with the regularized Euler logarithm of `Γ`. -/
def Eg (s : ℂ) : ℂ := (Real.log π : ℂ) * (-s / 2) + FleetDigammaSeries.regularizedLogGamma (s / 2)

theorem Gammaℝ_eq_exp {s : ℂ} (hs : 0 < s.re) : Gammaℝ s = cexp (Eg s) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hz : 0 < (s / 2).re := by simp; linarith
  rw [Gammaℝ_def, ← FleetGammaIdentification.exp_regularizedLogGamma _ hz, cpow_def_of_ne_zero hpi,
    ← Complex.ofReal_log Real.pi_pos.le, Eg, Complex.exp_add]

lemma abs_euler_le_one : |Real.eulerMascheroniConstant| ≤ 1 := by
  rw [_root_.abs_of_nonneg (by linarith [Real.one_half_lt_eulerMascheroniConstant])]
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

/-- The digamma series is `≤ 55` in norm on `{Re z ≥ 1/4, ‖z − 1‖ ≤ 8}`. -/
lemma norm_psiSeries_le {z : ℂ} (hz : 1 / 4 ≤ z.re) (hz1 : ‖z - 1‖ ≤ 8) :
    ‖-(Real.eulerMascheroniConstant : ℂ) - ∑' k : ℕ, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹)‖ ≤ 55 := by
  have h := FleetDigammaGrowth.norm_logDerivative_le (z := z) (δ := 1 / 4) (by norm_num) (by norm_num) hz
  have hl := Real.log_le_sub_one_of_pos (show 0 < 2 + ‖z - 1‖ by positivity)
  have hγ := abs_euler_le_one
  norm_num at h
  nlinarith

/-- The convex set on which the digamma bound is used. -/
def Kset : Set ℂ := {z : ℂ | 1 / 4 ≤ z.re} ∩ Metric.closedBall 1 8

lemma convex_Kset : Convex ℝ Kset := (convex_halfSpace_re_ge (r := 1 / 4)).inter (convex_closedBall _ _)

lemma half_mem_Kset {t : ℚ} (ht : |(t : ℝ)| ≤ 29 / 2) : sq t / 2 ∈ Kset := by
  refine ⟨?_, ?_⟩
  · show 1 / 4 ≤ (sq t / 2).re
    simp [sq]; norm_num
  · rw [Metric.mem_closedBall, dist_eq_norm]
    refine (Disc.norm_le_abs_re_add_abs_im _).trans ?_
    simp [sq]
    have : |(t : ℝ) / 2| ≤ 29 / 4 := by rw [abs_div]; norm_num; linarith
    norm_num at this ⊢
    linarith

/-- `‖log Γ(z₁) − log Γ(z₂)‖ ≤ 55 ‖z₁ − z₂‖` on `Kset`. -/
lemma regLogGamma_sub_le {z w : ℂ} (hz : z ∈ Kset) (hw : w ∈ Kset) :
    ‖FleetDigammaSeries.regularizedLogGamma z - FleetDigammaSeries.regularizedLogGamma w‖ ≤
      55 * ‖z - w‖ := by
  refine convex_Kset.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := FleetDigammaSeries.regularizedLogGamma)
    (f' := fun x => -(Real.eulerMascheroniConstant : ℂ) - ∑' k : ℕ, ((x + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹))
    (fun x hx => ?_) (fun x hx => ?_) hw hz
  · exact (FleetDigammaSeries.hasDerivAt_regularizedLogGamma
      (lt_of_lt_of_le (by norm_num) hx.1)).hasDerivWithinAt
  · refine norm_psiSeries_le hx.1 ?_
    have := hx.2; rwa [Metric.mem_closedBall, dist_eq_norm] at this


/-! ## The sign change -/

/-- Conjugate disc. -/
def conjD (D : Disc) : Disc := ⟨D.re, -D.im, D.r⟩

lemma conjD_contains {D : Disc} {z : ℂ} (h : D.Contains z) : (conjD D).Contains (conj z) := by
  unfold Contains at *
  have hc : (conjD D).c = conj D.c := by
    apply Complex.ext <;> simp [conjD, c]
  rw [hc, ← map_sub, Complex.norm_conj]
  simpa [conjD] using h

/-- The two heights `14.13` and `14.14`. -/
def t₁ : ℚ := 1413 / 100
def t₂ : ℚ := 707 / 50

/-- Disc for `ζ(1/2 + 14.13 i) · conj ζ(1/2 + 14.14 i)`. -/
def PD : Disc := mul (zetaD t₁) (conjD (zetaD t₂))

/-- The certificate: both point enclosures are valid, and `Re P + (3/5)‖P‖ < 0` on the disc. -/
def signOK : Bool :=
  zetaOK t₁ && zetaOK t₂ && decide (PD.re + PD.r + 6 / 10 * (PD.nb + PD.r) < 0)

set_option maxRecDepth 100000 in
theorem signOK_true : signOK = true := by decide +kernel

/-- `‖log Γ_ℝ(1/2 + 14.13 i) − log Γ_ℝ(1/2 + 14.14 i)‖ ≤ 3/10`. -/
theorem Eg_diff_le : ‖Eg (sq t₁) - Eg (sq t₂)‖ ≤ 3 / 10 := by
  have hd : sq t₁ - sq t₂ = -(1 / 100 : ℂ) * I := by
    simp only [sq, t₁, t₂]; push_cast; ring
  have hdn : ‖sq t₁ - sq t₂‖ = 1 / 100 := by
    rw [hd, norm_mul, Complex.norm_I, mul_one, norm_neg]; norm_num
  have e : Eg (sq t₁) - Eg (sq t₂) = (Real.log π : ℂ) * (-(sq t₁ - sq t₂) / 2) +
      (FleetDigammaSeries.regularizedLogGamma (sq t₁ / 2) -
        FleetDigammaSeries.regularizedLogGamma (sq t₂ / 2)) := by
    unfold Eg; ring
  have h1 : |((t₁ : ℚ) : ℝ)| ≤ 29 / 2 := by
    rw [abs_le]; simp only [t₁]; push_cast; constructor <;> norm_num
  have h2 : |((t₂ : ℚ) : ℝ)| ≤ 29 / 2 := by
    rw [abs_le]; simp only [t₂]; push_cast; constructor <;> norm_num
  have hL := regLogGamma_sub_le (half_mem_Kset h1) (half_mem_Kset h2)
  have hz : sq t₁ / 2 - sq t₂ / 2 = (sq t₁ - sq t₂) / 2 := by ring
  rw [hz, norm_div, hdn] at hL
  have hlog0 : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlog : Real.log π ≤ 43 / 20 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_d2]
  have hA : ‖(Real.log π : ℂ) * (-(sq t₁ - sq t₂) / 2)‖ ≤ 43 / 20 * (1 / 200) := by
    rw [norm_mul, norm_div, norm_neg, hdn, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog0]
    norm_num
    nlinarith
  rw [e]
  refine (norm_add_le _ _).trans ?_
  norm_num at hL
  linarith


/-- `Λ(1/2 + t i)` is real. -/
theorem completedZeta_half_line_im (t : ℝ) : (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).im = 0 := by
  have h1 : 1 - ((1 / 2 : ℂ) + t * I) = conj ((1 / 2 : ℂ) + t * I) := by
    apply Complex.ext <;> simp
    norm_num
  have h := completedRiemannZeta_one_sub ((1 / 2 : ℂ) + t * I)
  rw [h1, Kerr.ZetaConj.completedRiemannZeta_conj] at h
  exact Complex.conj_eq_iff_im.mp h

theorem completedZeta_eq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs)]

lemma continuous_completedZeta_half_line :
    Continuous fun t : ℝ => completedRiemannZeta ((1 / 2 : ℂ) + t * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have h0 : (1 / 2 : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h1 : (1 / 2 : ℂ) + t * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  exact (differentiableAt_completedZeta h0 h1).continuousAt.comp (x := t)
    (by fun_prop : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) + t * I) t)

lemma sq_eq (t : ℚ) : sq t = (1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I := by
  simp [sq]

/-- **The sign change**: `Λ(1/2 + 14.13 i) · Λ(1/2 + 14.14 i) < 0`. -/
theorem completedZeta_sign_change :
    (completedRiemannZeta (sq t₁)).re * (completedRiemannZeta (sq t₂)).re < 0 := by
  have hc := signOK_true
  simp only [signOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hz1, hz2⟩, hP⟩ := hc
  have d1 := zetaD_contains hz1
  have d2 := zetaD_contains hz2
  have dP : PD.Contains (riemannZeta (sq t₁) * conj (riemannZeta (sq t₂))) :=
    mul_contains d1 (conjD_contains d2)
  set P := riemannZeta (sq t₁) * conj (riemannZeta (sq t₂)) with hPdef
  -- `Re P + (3/5)‖P‖ < 0`
  have hPn := norm_le_of_contains dP
  have hPre : P.re ≤ (PD.re : ℝ) + PD.r := by
    have h := Complex.re_le_norm (P - PD.c)
    unfold Contains at dP
    simp only [sub_re, c_re] at h
    linarith
  have hP' : (PD.re : ℝ) + PD.r + 6 / 10 * ((PD.nb : ℝ) + PD.r) < 0 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hP; push_cast at this; linarith
  have hneg : P.re + 6 / 10 * ‖P‖ < 0 := by nlinarith
  -- the archimedean factor
  have hre1 : 0 < (sq t₁).re := by rw [sq_re]; norm_num
  have hre2 : 0 < (sq t₂).re := by rw [sq_re]; norm_num
  set E := Eg (sq t₁) - Eg (sq t₂) with hE
  have hEn : ‖E‖ ≤ 3 / 10 := Eg_diff_le
  have hexp : ‖cexp E - 1‖ ≤ 6 / 10 := by
    have := Complex.norm_exp_sub_one_le (x := E) (by linarith); linarith
  -- the product of the two real values
  set L1 := completedRiemannZeta (sq t₁)
  set L2 := completedRiemannZeta (sq t₂)
  have hi1 : L1.im = 0 := by
    show (completedRiemannZeta (sq t₁)).im = 0; rw [sq_eq]; exact completedZeta_half_line_im _
  have hi2 : L2.im = 0 := by
    show (completedRiemannZeta (sq t₂)).im = 0; rw [sq_eq]; exact completedZeta_half_line_im _
  have hprod : L1.re * L2.re = (L1 * conj L2).re := by
    simp [Complex.mul_re, hi1, hi2]
  have hG2 : cexp (Eg (sq t₂)) * conj (cexp (Eg (sq t₂))) = ((Complex.normSq (cexp (Eg (sq t₂))) : ℝ) : ℂ) :=
    Complex.mul_conj _
  have hfac : L1 * conj L2 = ((Complex.normSq (cexp (Eg (sq t₂))) : ℝ) : ℂ) * (cexp E * P) := by
    simp only [L1, L2]
    rw [completedZeta_eq_mul hre1, completedZeta_eq_mul hre2, Gammaℝ_eq_exp hre1, Gammaℝ_eq_exp hre2,
      ← hG2, hPdef, hE, Complex.exp_sub, map_mul]
    have : cexp (Eg (sq t₂)) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hpos : 0 < Complex.normSq (cexp (Eg (sq t₂))) :=
    Complex.normSq_pos.mpr (Complex.exp_ne_zero _)
  have hreE : (cexp E * P).re < 0 := by
    have hsplit : cexp E * P = P + (cexp E - 1) * P := by ring
    rw [hsplit, Complex.add_re]
    have := Complex.re_le_norm ((cexp E - 1) * P)
    rw [norm_mul] at this
    have := mul_le_mul_of_nonneg_right hexp (norm_nonneg P)
    linarith
  rw [hprod, hfac, Complex.re_ofReal_mul]
  exact mul_neg_of_pos_of_neg hpos hreE

/-- **A nontrivial zero of `ζ` on the critical line, with ordinate in `(14.13, 14.14)`.** -/
theorem exists_zeta_zero_first :
    ∃ t : ℝ, 1413 / 100 < t ∧ t < 1414 / 100 ∧ riemannZeta ((1 / 2 : ℂ) + t * I) = 0 := by
  set f : ℝ → ℝ := fun t => (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re with hf
  have hcont : Continuous f := Complex.continuous_re.comp continuous_completedZeta_half_line
  have hs := completedZeta_sign_change
  have ha : f ((t₁ : ℚ) : ℝ) = (completedRiemannZeta (sq t₁)).re := by rw [hf, sq_eq]
  have hb : f ((t₂ : ℚ) : ℝ) = (completedRiemannZeta (sq t₂)).re := by rw [hf, sq_eq]
  rw [← ha, ← hb] at hs
  have hab : ((t₁ : ℚ) : ℝ) ≤ ((t₂ : ℚ) : ℝ) := by simp only [t₁, t₂]; push_cast; norm_num
  have hzero : ∃ t ∈ Set.Icc ((t₁ : ℚ) : ℝ) ((t₂ : ℚ) : ℝ), f t = 0 := by
    rcases lt_or_gt_of_ne (show f ((t₁ : ℚ) : ℝ) ≠ 0 by intro h; rw [h] at hs; simp at hs) with h1 | h1
    · have h2 : 0 < f ((t₂ : ℚ) : ℝ) := by nlinarith
      exact intermediate_value_Icc hab hcont.continuousOn ⟨h1.le, h2.le⟩
    · have h2 : f ((t₂ : ℚ) : ℝ) < 0 := by nlinarith
      exact intermediate_value_Icc' hab hcont.continuousOn ⟨h2.le, h1.le⟩
  obtain ⟨t, ⟨ht1, ht2⟩, hft⟩ := hzero
  have hne1 : t ≠ ((t₁ : ℚ) : ℝ) := by rintro rfl; rw [hft] at hs; simp at hs
  have hne2 : t ≠ ((t₂ : ℚ) : ℝ) := by rintro rfl; rw [hft] at hs; simp at hs
  have e1 : ((t₁ : ℚ) : ℝ) = 1413 / 100 := by simp only [t₁]; push_cast; ring
  have e2 : ((t₂ : ℚ) : ℝ) = 1414 / 100 := by simp only [t₂]; push_cast; norm_num
  refine ⟨t, by rw [← e1]; exact lt_of_le_of_ne ht1 (Ne.symm hne1),
    by rw [← e2]; exact lt_of_le_of_ne ht2 hne2, ?_⟩
  have hre : 0 < ((1 / 2 : ℂ) + t * I).re := by simp
  have hL : completedRiemannZeta ((1 / 2 : ℂ) + t * I) = 0 :=
    Complex.ext hft (completedZeta_half_line_im t)
  have h0 : (1 / 2 : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [riemannZeta_def_of_ne_zero h0, hL, zero_div]


/-- **The first zero as a nontrivial zero**: `ρ = 1/2 + t i` with `14.13 < t < 14.14`. -/
theorem exists_nontrivialZero_first :
    ∃ ρ : ℂ, Reduction.IsNontrivialZero ρ ∧ ρ.re = 1 / 2 ∧ 1413 / 100 < ρ.im ∧ ρ.im < 1414 / 100 := by
  obtain ⟨t, ht1, ht2, hz⟩ := exists_zeta_zero_first
  refine ⟨(1 / 2 : ℂ) + t * I, ⟨hz, ?_, ?_⟩, by simp, by simpa using ht1, by simpa using ht2⟩
  · rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    have h0 : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · intro h
    have := congrArg Complex.re h
    simp at this

end FleetFirstZero
