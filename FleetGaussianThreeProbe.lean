import FleetRationalBankCriterion
import FleetFiniteProbeCertificate
import Mathlib

/-! A three-Gaussian detector. It is nonpositive on every real spectrum and has
an explicit nonnegative response on a centered vertically displaced symmetric
pair. A selected pair does not control the total zero sum: the final margin
lemma retains an explicit bound for the remaining contribution. -/

noncomputable section
open Complex Finset GaussianTest

namespace FleetGaussianThreeProbe

def H (b q : ℝ) (z : ℂ) : ℂ :=
  (Real.sqrt (Real.pi/b):ℂ)*Complex.exp (-(z-q)^2/(4*b))

def coefficient (b h : ℝ) : ℝ := Real.exp (h^2/(4*b))

def detector (b T h : ℝ) (z : ℂ) : ℂ :=
  2*H b T z-(coefficient b h:ℂ)*(H b (T-h) z+H b (T+h) z)

lemma H_eq_transform {b : ℝ} (hb : 0 < b) (q : ℝ) (z : ℂ) :
    H b q z = FleetFullLineFourier.h (gauss b q) z :=
  (FleetGaussianDictionaryMember.h_gauss_eq hb q z).symm

lemma H_real (b q x : ℝ) :
    H b q x = (Real.sqrt (Real.pi/b)*Real.exp (-(x-q)^2/(4*b)):ℝ) := by
  unfold H
  push_cast
  rfl

lemma coefficient_pos (b h : ℝ) : 0 < coefficient b h := Real.exp_pos _

lemma coefficient_neg (b h : ℝ) : coefficient b (-h) = coefficient b h := by
  simp [coefficient]

lemma scaled_shift {b : ℝ} (hb : 0 < b) (T h : ℝ) (z : ℂ) :
    (coefficient b h:ℂ)*H b (T+h) z =
      H b T z*Complex.exp ((h:ℂ)*(z-T)/(2*b)) := by
  have hb0 : (b:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have he : (h:ℂ)^2/(4*b)-(z-((T:ℂ)+h))^2/(4*b) =
      -(z-T)^2/(4*b)+(h:ℂ)*(z-T)/(2*b) := by field_simp; ring
  unfold coefficient H
  push_cast
  calc
    _ = (Real.sqrt (Real.pi/b):ℂ)*
        Complex.exp ((h:ℂ)^2/(4*b)-(z-((T:ℂ)+h))^2/(4*b)) := by
      rw [Complex.exp_sub]
      simp only [neg_div, Complex.exp_neg]
      ring
    _ = _ := by rw [he, Complex.exp_add]; ring

theorem detector_eq_cosh {b : ℝ} (hb : 0 < b) (T h : ℝ) (z : ℂ) :
    detector b T h z =
      2*H b T z*(1-Complex.cosh ((h:ℂ)*(z-T)/(2*b))) := by
  have hl := scaled_shift hb T (-h) z
  rw [coefficient_neg, show T+(-h) = T-h by ring] at hl
  have hr := scaled_shift hb T h z
  unfold detector
  rw [mul_add, hl, hr]
  rw [Complex.cosh]
  push_cast
  ring_nf

theorem detector_real_eq {b : ℝ} (hb : 0 < b) (T h x : ℝ) :
    detector b T h x =
      (2*(Real.sqrt (Real.pi/b)*Real.exp (-(x-T)^2/(4*b)))*
        (1-Real.cosh (h*(x-T)/(2*b))):ℝ) := by
  rw [detector_eq_cosh hb, H_real]
  push_cast
  rfl

/-- Every real unit atom, and therefore every positive weighted real atom,
has a nonpositive detector value. -/
theorem detector_real_nonpos {b : ℝ} (hb : 0 < b) (T h x : ℝ) :
    (detector b T h x).re ≤ 0 := by
  rw [detector_real_eq hb]
  simp only [Complex.ofReal_re]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (sub_nonpos.mpr (Real.one_le_cosh _))

theorem detector_displaced {b : ℝ} (hb : 0 < b) (T h δ : ℝ) :
    detector b T h ((T:ℂ)+(δ:ℂ)*I) =
      (2*Real.sqrt (Real.pi/b)*Real.exp (δ^2/(4*b))*
        (1-Real.cos (h*δ/(2*b))):ℝ) := by
  have he : -(((T:ℂ)+(δ:ℂ)*I)-T)^2/(4*b) = ((δ^2/(4*b):ℝ):ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  have hh : H b T ((T:ℂ)+(δ:ℂ)*I) =
      (Real.sqrt (Real.pi/b)*Real.exp (δ^2/(4*b)):ℝ) := by
    unfold H
    rw [he, ← Complex.ofReal_exp]
    push_cast
    rfl
  have ha : (h:ℂ)*(((T:ℂ)+(δ:ℂ)*I)-T)/(2*b) =
      ((h*δ/(2*b):ℝ):ℂ)*I := by push_cast; ring
  rw [detector_eq_cosh hb, hh, ha, Complex.cosh_mul_I, ← Complex.ofReal_cos]
  push_cast
  ring

def pairSignal (b h δ : ℝ) : ℝ :=
  4*Real.sqrt (Real.pi/b)*Real.exp (δ^2/(4*b))*(1-Real.cos (h*δ/(2*b)))

/-- The symmetric vertically displaced pair has a nonnegative detector
response. It vanishes at the exact resonances `h*δ/(2*b) ∈ 2*pi*ℤ`. -/
theorem detector_displaced_pair {b : ℝ} (hb : 0 < b) (T h δ : ℝ) :
    detector b T h ((T:ℂ)+(δ:ℂ)*I)+detector b T h ((T:ℂ)-(δ:ℂ)*I) =
      (pairSignal b h δ:ℂ) := by
  have he : (T:ℂ)-(δ:ℂ)*I = (T:ℂ)+((-δ:ℝ):ℂ)*I := by push_cast; ring
  rw [he, detector_displaced hb, detector_displaced hb]
  simp only [neg_sq, mul_neg, neg_div, Real.cos_neg]
  unfold pairSignal
  push_cast
  ring

lemma pairSignal_nonneg (b h δ : ℝ) : 0 ≤ pairSignal b h δ := by
  unfold pairSignal
  exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))

lemma detector_shift_real_neg {b h : ℝ} (hb : 0 < b) (hh : h ≠ 0) (T : ℝ) :
    (detector b T h (T+h)).re < 0 := by
  rw [← Complex.ofReal_add, detector_real_eq hb]
  simp only [Complex.ofReal_re]
  have ha : h*((T+h)-T)/(2*b) ≠ 0 := by
    rw [show h*((T+h)-T)/(2*b) = h^2/(2*b) by ring]
    exact ne_of_gt (div_pos (sq_pos_of_ne_zero hh) (by positivity))
  exact mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr (Real.one_lt_cosh.mpr ha))

/-- An explicit limitation of this one detector: without a background mass
restriction, sufficiently many repetitions of the real atom `T+h` cancel
any prescribed positive signal. These are unit atoms, not fractional weights. -/
theorem exists_repeated_real_background {b h : ℝ} (hb : 0 < b) (hh : h ≠ 0)
    (T signal : ℝ) :
    ∃ N : ℕ, signal+(∑ _i : Fin N, (detector b T h (T+h)).re) ≤ 0 := by
  have hd := detector_shift_real_neg hb hh T
  obtain ⟨N,hN⟩ := exists_nat_gt (signal/(-(detector b T h (T+h)).re))
  have hp : signal < (N:ℝ)*(-(detector b T h (T+h)).re) :=
    (div_lt_iff₀ (by linarith)).mp hN
  refine ⟨N, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

lemma finite_trace_nonpos {b : ℝ} (hb : 0 < b) (T h : ℝ)
    {N : ℕ} (x : Fin N → ℝ) :
    2*(∑ i, H b T (x i)).re-coefficient b h*
      ((∑ i, H b (T-h) (x i)).re+(∑ i, H b (T+h) (x i)).re) ≤ 0 := by
  have hs : (∑ i, (detector b T h (x i)).re) ≤ 0 :=
    sum_nonpos (fun _ _ => detector_real_nonpos hb T h _)
  simpa only [detector, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
    Complex.add_re, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Complex.re_sum] using hs

/-- Weak duality for this explicit detector. No mass bound is needed, since
the detector's continuum upper bound is zero. -/
theorem three_residual_inequality {b : ℝ} (hb : 0 < b) (T h : ℝ)
    {N : ℕ} (x : Fin N → ℝ) (A₀ Am Ap : ℂ) (ε : ℝ)
    (h₀ : ‖(∑ i, H b T (x i))-A₀‖ ≤ ε)
    (hm : ‖(∑ i, H b (T-h) (x i))-Am‖ ≤ ε)
    (hp : ‖(∑ i, H b (T+h) (x i))-Ap‖ ≤ ε) :
    2*A₀.re-coefficient b h*(Am.re+Ap.re) ≤ ε*(2+2*coefficient b h) := by
  have hc : A₀.re-(∑ i, H b T (x i)).re ≤ ε := by
    calc
      _ ≤ ‖A₀-(∑ i, H b T (x i))‖ := Complex.re_le_norm _
      _ = ‖(∑ i, H b T (x i))-A₀‖ := norm_sub_rev _ _
      _ ≤ ε := h₀
  have hl : (∑ i, H b (T-h) (x i)).re-Am.re ≤ ε :=
    (Complex.re_le_norm _).trans hm
  have hr : (∑ i, H b (T+h) (x i)).re-Ap.re ≤ ε :=
    (Complex.re_le_norm _).trans hp
  have hside := mul_le_mul_of_nonneg_left (add_le_add hl hr) (coefficient_pos b h).le
  have ht := finite_trace_nonpos hb T h x
  linarith

def arithmeticDetector (b T h : ℝ) : ℝ :=
  2*(FleetFullLineArithmetic.rhs (gauss b T)).re-coefficient b h*
    ((FleetFullLineArithmetic.rhs (gauss b (T-h))).re+
      (FleetFullLineArithmetic.rhs (gauss b (T+h))).re)

/-- An actual rational-bank feasibility statement forces the displayed
arithmetic inequality. Its right side includes the entire coefficient `l1`
error penalty; the weighted mass budget cancels. -/
theorem stage_inequality {b M : ℝ} (hb : 0 < b) {n : ℕ}
    (hf : FleetRationalBankCriterion.Feasible b M n) (T h : ℚ)
    (hT : T ∈ FleetRationalBanks.bank n)
    (hL : T-h ∈ FleetRationalBanks.bank n)
    (hR : T+h ∈ FleetRationalBanks.bank n) :
    arithmeticDetector b T h ≤ (2+2*coefficient b h)/((n:ℝ)+1) := by
  obtain ⟨N,x,_,hr⟩ := hf
  have h0 := hr T hT
  have hl := hr (T-h) hL
  have hh := hr (T+h) hR
  simp only [Rat.cast_sub, Rat.cast_add] at hl hh
  simp_rw [← H_eq_transform hb] at h0 hl hh
  have hout := three_residual_inequality hb (T:ℝ) (h:ℝ) x
    (FleetFullLineArithmetic.rhs (gauss b T))
    (FleetFullLineArithmetic.rhs (gauss b ((T:ℝ)-h)))
    (FleetFullLineArithmetic.rhs (gauss b ((T:ℝ)+h)))
    (1/((n:ℝ)+1)) h0 hl hh
  simpa only [arithmeticDetector, one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hout

theorem infeasible_of_stage_gap {b M : ℝ} (hb : 0 < b) {n : ℕ} (T h : ℚ)
    (hT : T ∈ FleetRationalBanks.bank n)
    (hL : T-h ∈ FleetRationalBanks.bank n)
    (hR : T+h ∈ FleetRationalBanks.bank n)
    (hgap : (2+2*coefficient b h)/((n:ℝ)+1) < arithmeticDetector b T h) :
    ¬ FleetRationalBankCriterion.Feasible b M n := by
  intro hf
  exact (not_lt_of_ge (stage_inequality hb hf T h hT hL hR)) hgap

/-- A selected positive pair response cannot be used alone: the remaining
contribution must have a proved lower bound. This is only the exact algebraic
margin implication, and asserts no zero-sum identity or background estimate. -/
theorem background_margin_impossible {signal background total B ε η L : ℝ}
    (hdecomp : total = signal+background)
    (hbackground : -B ≤ background)
    (hupper : total ≤ (ε+η)*L)
    (hgap : B+(ε+η)*L < signal) : False := by
  linarith

end FleetGaussianThreeProbe
