/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import Mathlib

/-!
# Kusmin–Landau and van der Corput's second-derivative test (discrete form)

New file (written for this repo). `ee t = e^{2πit}`.

* `kusmin_landau`: if the differences `g(n) = F(n+1) − F(n)` are nondecreasing on `[u, v]` and
  stay in `[k + δ, k + 1 − δ]` for an integer `k`, then `‖∑_{u ≤ n ≤ v} e(F(n))‖ ≤ 1 + 1/δ`.
  Proof: `e(F n) = c_n (e(F(n+1)) − e(F n))` with `c_n = −1/2 − (i/2) cot(π g_n)`, partial summation,
  and monotonicity of `cot` on `(0, π)` (via `sin(π(y₂ − y₁)) ≥ 0`).
* `vdc_second_derivative`: if `g(n+1) − g(n) ≥ λ > 0` on `[N₁, N₂]`, then for `0 < δ ≤ 1/2`
  `‖∑_{N₁ ≤ n ≤ N₂} e(F(n))‖ ≤ (g(N₂) − g(N₁) + 2)(2δ/λ + 2 + 1/δ)`.
  Proof: classify `n` by the integer `⌊g(n) + δ⌋`; on each class the `n` with `g(n)` within `δ`
  of that integer number at most `2δ/λ + 1`, the others form an interval where Kusmin–Landau applies.
-/

noncomputable section
open Complex Finset

namespace Kerr.PowerfulNumbers

/-- `e(t) = exp(2πit)`. -/
def ee (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I)

lemma norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  rw [ee, Complex.norm_exp_ofReal_mul_I]

lemma ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  rw [ee, ee, ee, ← Complex.exp_add]; congr 1; push_cast; ring

lemma ee_int (k : ℤ) : ee k = 1 := by
  rw [ee]
  have : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * I) = (k : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma ee_eq (t : ℝ) : ee t = (Real.cos (2 * Real.pi * t) : ℂ) + (Real.sin (2 * Real.pi * t) : ℂ) * I := by
  rw [ee, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- `cot(π y)` written as `cos/sin`. -/
def cotp (y : ℝ) : ℝ := Real.cos (Real.pi * y) / Real.sin (Real.pi * y)

/-- The Kusmin–Landau coefficient `c(y) = −1/2 − (i/2) cot(π y)`, so that `c(y)(e(y) − 1) = 1`. -/
def klc (y : ℝ) : ℂ := -1 / 2 - ((cotp y / 2 : ℝ) : ℂ) * I

lemma klc_mul {y : ℝ} (hs : Real.sin (Real.pi * y) ≠ 0) : klc y * (ee y - 1) = 1 := by
  rw [klc, ee_eq, cotp]
  have h2 : 2 * Real.pi * y = 2 * (Real.pi * y) := by ring
  rw [h2, Real.cos_two_mul, Real.sin_two_mul]
  set s := Real.sin (Real.pi * y)
  set c := Real.cos (Real.pi * y)
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.one_re,
      Complex.sub_im, Complex.add_im, Complex.one_im]
    norm_num
    field_simp
    nlinarith [hsc]
  · simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.one_re,
      Complex.sub_im, Complex.add_im, Complex.one_im]
    norm_num
    field_simp
    linear_combination (-2 * c) * hsc

/-- `sin(π y) ≥ 2δ` for `y ∈ [δ, 1 − δ]`. -/
lemma sin_pi_ge {δ y : ℝ} (hδ : 0 ≤ δ) (h1 : δ ≤ y) (h2 : y ≤ 1 - δ) :
    2 * δ ≤ Real.sin (Real.pi * y) := by
  rcases le_or_gt y (1 / 2) with hy | hy
  · have := Real.mul_le_sin (x := Real.pi * y) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    rw [show 2 / Real.pi * (Real.pi * y) = 2 * y by field_simp] at this
    linarith
  · have e : Real.sin (Real.pi * y) = Real.sin (Real.pi * (1 - y)) := by
      rw [show Real.pi * (1 - y) = Real.pi - Real.pi * y by ring, Real.sin_pi_sub]
    have := Real.mul_le_sin (x := Real.pi * (1 - y)) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    rw [show 2 / Real.pi * (Real.pi * (1 - y)) = 2 * (1 - y) by field_simp] at this
    linarith

lemma abs_cotp_le {δ y : ℝ} (hδ : 0 < δ) (h1 : δ ≤ y) (h2 : y ≤ 1 - δ) :
    |cotp y| ≤ 1 / (2 * δ) := by
  have hs := sin_pi_ge hδ.le h1 h2
  have hs0 : 0 < Real.sin (Real.pi * y) := by linarith
  rw [cotp, abs_div, abs_of_pos hs0]
  rw [div_le_div_iff₀ hs0 (by positivity)]
  have := Real.abs_cos_le_one (Real.pi * y)
  nlinarith

/-- `cot(π ·)` is antitone on `(0, 1)`. -/
lemma cotp_anti {y₁ y₂ : ℝ} (h0 : 0 < y₁) (h12 : y₁ ≤ y₂) (h2 : y₂ < 1) : cotp y₂ ≤ cotp y₁ := by
  have hs1 : 0 < Real.sin (Real.pi * y₁) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hs2 : 0 < Real.sin (Real.pi * y₂) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hd : 0 ≤ Real.sin (Real.pi * y₂ - Real.pi * y₁) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rw [Real.sin_sub] at hd
  rw [cotp, cotp, div_le_div_iff₀ hs2 hs1]
  nlinarith

lemma norm_klc_le {δ y : ℝ} (hδ : 0 < δ) (h1 : δ ≤ y) (h2 : y ≤ 1 - δ) :
    ‖klc y‖ ≤ 1 / 2 + 1 / (4 * δ) := by
  rw [klc]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    show ‖(-1 / 2 : ℂ)‖ = 1 / 2 by norm_num, abs_div, abs_two]
  have := abs_cotp_le hδ h1 h2
  have e : 1 / (4 * δ) = 1 / (2 * δ) / 2 := by field_simp; ring
  linarith

lemma sum_Ico_telescope (a : ℕ → ℝ) {u v : ℕ} (huv : u ≤ v) :
    ∑ n ∈ Ico u v, (a n - a (n + 1)) = a u - a v := by
  induction v, huv using Nat.le_induction with
  | base => simp
  | succ v huv ih => rw [Finset.sum_Ico_succ_top huv, ih]; ring

/-- **Kusmin–Landau inequality** (discrete form). -/
theorem kusmin_landau {F : ℕ → ℝ} {u v : ℕ} (huv : u ≤ v) {δ : ℝ} (hδ0 : 0 < δ) (k : ℤ)
    (hg : ∀ n, u ≤ n → n ≤ v → (k : ℝ) + δ ≤ F (n + 1) - F n ∧ F (n + 1) - F n ≤ k + 1 - δ)
    (hmono : ∀ n, u ≤ n → n < v → F (n + 1) - F n ≤ F (n + 2) - F (n + 1)) :
    ‖∑ n ∈ Icc u v, ee (F n)‖ ≤ 1 + 1 / δ := by
  set y : ℕ → ℝ := fun n => F (n + 1) - F n - k with hy
  have hyr : ∀ n, u ≤ n → n ≤ v → δ ≤ y n ∧ y n ≤ 1 - δ := by
    intro n h1 h2; have := hg n h1 h2; simp only [hy]; constructor <;> linarith [this.1, this.2]
  set E : ℕ → ℂ := fun n => ee (F n) with hE
  set c : ℕ → ℂ := fun n => klc (y n) with hc
  have hkey : ∀ n, u ≤ n → n ≤ v → E n = c n * (E (n + 1) - E n) := by
    intro n h1 h2
    have hs : Real.sin (Real.pi * y n) ≠ 0 := by
      have := sin_pi_ge hδ0.le (hyr n h1 h2).1 (hyr n h1 h2).2; linarith
    have hE1 : E (n + 1) = E n * ee (y n) := by
      simp only [hE, hy]
      rw [← ee_add, show F n + (F (n + 1) - F n - k) = F (n + 1) + (-k : ℤ) by push_cast; ring,
        ee_add, ee_int, mul_one]
    rw [hE1, show E n * ee (y n) - E n = E n * (ee (y n) - 1) by ring, mul_left_comm,
      klc_mul hs, mul_one]
  -- partial summation
  have hW : ∀ m, u ≤ m → m ≤ v → ∑ n ∈ Icc u m, E n - c m * E (m + 1) =
      -(c u * E u) + ∑ n ∈ Ico u m, (c n - c (n + 1)) * E (n + 1) := by
    intro m hum hmv
    induction m, hum using Nat.le_induction with
    | base =>
      simp only [Finset.Icc_self, sum_singleton, Finset.Ico_self, sum_empty, add_zero]
      have := hkey u le_rfl (by omega)
      linear_combination this
    | succ m hum ih =>
      have ih' := ih (by omega)
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Ico_succ_top hum]
      have := hkey (m + 1) (by omega) hmv
      linear_combination ih' + this
  have hcu := norm_klc_le hδ0 (hyr u le_rfl huv).1 (hyr u le_rfl huv).2
  have hcv := norm_klc_le hδ0 (hyr v huv le_rfl).1 (hyr v huv le_rfl).2
  have hdiff : ∀ n ∈ Ico u v, ‖(c n - c (n + 1)) * E (n + 1)‖ =
      (cotp (y n) - cotp (y (n + 1))) / 2 := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Ico.mp hn
    rw [norm_mul, hE, norm_ee, mul_one]
    have hmn : y n ≤ y (n + 1) := by
      simp only [hy]; have := hmono n h1 h2; linarith
    have hanti := cotp_anti (by linarith [(hyr n h1 h2.le).1]) hmn
      (by linarith [(hyr (n + 1) (by omega) h2).2])
    have : c n - c (n + 1) = (((cotp (y (n + 1)) - cotp (y n)) / 2 : ℝ) : ℂ) * I := by
      simp only [hc, klc]; push_cast; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  have hsum : ‖∑ n ∈ Ico u v, (c n - c (n + 1)) * E (n + 1)‖ ≤ 1 / (2 * δ) := by
    refine (norm_sum_le _ _).trans ?_
    rw [sum_congr rfl hdiff, ← sum_div, sum_Ico_telescope (fun n => cotp (y n)) huv]
    have := abs_cotp_le hδ0 (hyr u le_rfl huv).1 (hyr u le_rfl huv).2
    have := abs_cotp_le hδ0 (hyr v huv le_rfl).1 (hyr v huv le_rfl).2
    have e : 1 / (2 * δ) = (1 / (2 * δ) + 1 / (2 * δ)) / 2 := by ring
    rw [e]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith [abs_le.mp ‹|cotp (y u)| ≤ 1 / (2 * δ)›, abs_le.mp ‹|cotp (y v)| ≤ 1 / (2 * δ)›]
  have hS : ∑ n ∈ Icc u v, E n = (-(c u * E u) + ∑ n ∈ Ico u v, (c n - c (n + 1)) * E (n + 1)) +
      c v * E (v + 1) := by
    rw [← hW v huv le_rfl]; ring
  rw [hS]
  calc ‖(-(c u * E u) + ∑ n ∈ Ico u v, (c n - c (n + 1)) * E (n + 1)) + c v * E (v + 1)‖
      ≤ ‖c u * E u‖ + ‖∑ n ∈ Ico u v, (c n - c (n + 1)) * E (n + 1)‖ + ‖c v * E (v + 1)‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans ?_) le_rfl
        rw [norm_neg]
    _ ≤ (1 / 2 + 1 / (4 * δ)) + 1 / (2 * δ) + (1 / 2 + 1 / (4 * δ)) := by
        rw [norm_mul, norm_mul, hE, norm_ee, norm_ee, mul_one, mul_one]
        exact add_le_add (add_le_add hcu hsum) hcv
    _ = 1 + 1 / δ := by field_simp; ring

lemma eq_Icc_of_ordConnected {S : Finset ℕ} (hS : S.Nonempty)
    (hc : ∀ a ∈ S, ∀ b ∈ S, ∀ n, a ≤ n → n ≤ b → n ∈ S) : S = Icc (S.min' hS) (S.max' hS) := by
  ext n
  constructor
  · intro hn; exact mem_Icc.mpr ⟨S.min'_le n hn, S.le_max' n hn⟩
  · intro hn
    obtain ⟨h1, h2⟩ := mem_Icc.mp hn
    exact hc _ (S.min'_mem hS) _ (S.max'_mem hS) n h1 h2

/-- **van der Corput's second-derivative test** (discrete form). With `g(n) = F(n+1) − F(n)` and
`g(n+1) − g(n) ≥ λ > 0` on `[N₁, N₂]`, for `0 < δ ≤ 1/2`:
`‖∑_{N₁ ≤ n ≤ N₂} e(F n)‖ ≤ (g(N₂) − g(N₁) + 2)(2δ/λ + 2 + 1/δ)`. -/
theorem vdc_second_derivative {F : ℕ → ℝ} {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) {lam δ : ℝ}
    (hlam : 0 < lam) (hδ0 : 0 < δ)
    (hstep : ∀ n, N₁ ≤ n → n < N₂ → lam ≤ (F (n + 2) - F (n + 1)) - (F (n + 1) - F n)) :
    ‖∑ n ∈ Icc N₁ N₂, ee (F n)‖ ≤
      ((F (N₂ + 1) - F N₂) - (F (N₁ + 1) - F N₁) + 2) * (2 * δ / lam + 2 + 1 / δ) := by
  set g : ℕ → ℝ := fun n => F (n + 1) - F n with hg
  have hgrow : ∀ n m, N₁ ≤ n → n ≤ m → m ≤ N₂ → lam * ((m : ℝ) - n) ≤ g m - g n := by
    intro n m hn hnm hm
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hnm ih =>
      have h1 := hstep m (by omega) (by omega)
      have ih' := ih (by omega)
      simp only [hg] at h1 ih' ⊢
      push_cast
      linarith
  have hmono : ∀ n m, N₁ ≤ n → n ≤ m → m ≤ N₂ → g n ≤ g m := by
    intro n m h1 h2 h3
    have h := hgrow n m h1 h2 h3
    have : (0 : ℝ) ≤ lam * ((m : ℝ) - n) :=
      mul_nonneg hlam.le (by have : (n : ℝ) ≤ m := by exact_mod_cast h2
                             linarith)
    linarith
  set κ : ℕ → ℤ := fun n => ⌊g n + δ⌋ with hκ
  have hκmono : ∀ n m, N₁ ≤ n → n ≤ m → m ≤ N₂ → κ n ≤ κ m :=
    fun n m h1 h2 h3 => Int.floor_mono (by linarith [hmono n m h1 h2 h3])
  have hmaps : ∀ n ∈ Icc N₁ N₂, κ n ∈ Finset.Icc (κ N₁) (κ N₂) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨hκmono _ _ le_rfl h1 h2, hκmono _ _ h1 h2 le_rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hclass : ∀ k ∈ Finset.Icc (κ N₁) (κ N₂),
      ‖∑ n ∈ (Icc N₁ N₂).filter (fun n => κ n = k), ee (F n)‖ ≤ 2 * δ / lam + 2 + 1 / δ := by
    intro k _
    set S := (Icc N₁ N₂).filter (fun n => κ n = k) with hS
    have hmemS : ∀ n ∈ S, (N₁ ≤ n ∧ n ≤ N₂) ∧ (k : ℝ) ≤ g n + δ ∧ g n + δ < k + 1 := by
      intro n hn
      simp only [hS, mem_filter, mem_Icc] at hn
      obtain ⟨h1, h2⟩ := hn
      have := Int.floor_eq_iff.mp h2
      exact ⟨h1, this.1, this.2⟩
    rw [← Finset.sum_filter_add_sum_filter_not S (fun n => g n < k + δ)]
    have hbad : ‖∑ n ∈ S.filter (fun n => g n < k + δ), ee (F n)‖ ≤ 2 * δ / lam + 1 := by
      set B := S.filter (fun n => g n < k + δ) with hB
      refine (norm_sum_le _ _).trans ?_
      simp only [norm_ee, sum_const, nsmul_eq_mul, mul_one]
      rcases B.eq_empty_or_nonempty with hB0 | hBne
      · rw [hB0]; simp only [card_empty, Nat.cast_zero]; positivity
      set a := B.min' hBne with ha
      have haB := B.min'_mem hBne
      have hsub : B ⊆ Icc a (a + ⌊2 * δ / lam⌋₊) := by
        intro n hn
        have hna : a ≤ n := B.min'_le n hn
        refine mem_Icc.mpr ⟨hna, ?_⟩
        have hn' : n ∈ S ∧ g n < k + δ := mem_filter.mp hn
        have haB' : a ∈ S ∧ g a < k + δ := mem_filter.mp haB
        obtain ⟨⟨hn1, hn2⟩, -, -⟩ := hmemS n hn'.1
        obtain ⟨⟨ha1, -⟩, hka, -⟩ := hmemS a haB'.1
        have hgr := hgrow a n ha1 hna hn2
        have hlt : lam * ((n : ℝ) - a) < 2 * δ := by linarith [hn'.2]
        have hlt' : ((n - a : ℕ) : ℝ) ≤ 2 * δ / lam := by
          rw [Nat.cast_sub hna, le_div_iff₀ hlam]; linarith
        have := Nat.le_floor hlt'
        omega
      have hc := card_le_card hsub
      rw [Nat.card_Icc] at hc
      have hc' : (B.card : ℝ) ≤ ⌊2 * δ / lam⌋₊ + 1 := by exact_mod_cast (by omega : B.card ≤ ⌊2 * δ / lam⌋₊ + 1)
      linarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * δ / lam)]
    have hgood : ‖∑ n ∈ S.filter (fun n => ¬ g n < k + δ), ee (F n)‖ ≤ 1 + 1 / δ := by
      set G := S.filter (fun n => ¬ g n < k + δ) with hG
      rcases G.eq_empty_or_nonempty with hG0 | hGne
      · rw [hG0, sum_empty, norm_zero]; positivity
      have hmemG : ∀ n ∈ G, (N₁ ≤ n ∧ n ≤ N₂) ∧ (k : ℝ) + δ ≤ g n ∧ g n + δ < k + 1 := by
        intro n hn
        have hn' : n ∈ S ∧ ¬ g n < k + δ := mem_filter.mp hn
        obtain ⟨h1, -, h3⟩ := hmemS n hn'.1
        exact ⟨h1, by push Not at hn'; linarith [hn'.2], h3⟩
      have hconv : ∀ a ∈ G, ∀ b ∈ G, ∀ n, a ≤ n → n ≤ b → n ∈ G := by
        intro a ha b hb n han hnb
        obtain ⟨⟨ha1, ha2⟩, ha3, ha4⟩ := hmemG a ha
        obtain ⟨⟨hb1, hb2⟩, hb3, hb4⟩ := hmemG b hb
        have h1 := hmono a n ha1 han (hnb.trans hb2)
        have h2 := hmono n b (ha1.trans han) hnb hb2
        refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨ha1.trans han, hnb.trans hb2⟩, ?_⟩, ?_⟩
        · exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
        · push Not; linarith
      rw [eq_Icc_of_ordConnected hGne hconv]
      have huv : G.min' hGne ≤ G.max' hGne := G.min'_le _ (G.max'_mem hGne)
      refine kusmin_landau huv hδ0 k (fun n h1 h2 => ?_) (fun n h1 h2 => ?_)
      · have hn := hconv _ (G.min'_mem hGne) _ (G.max'_mem hGne) n h1 h2
        obtain ⟨-, h3, h4⟩ := hmemG n hn
        exact ⟨h3, by linarith⟩
      · have hu := (hmemG _ (G.min'_mem hGne)).1.1
        have hv := (hmemG _ (G.max'_mem hGne)).1.2
        exact hmono n (n + 1) (hu.trans h1) (by omega) (by omega)
    calc _ ≤ ‖∑ n ∈ S.filter (fun n => g n < k + δ), ee (F n)‖ +
          ‖∑ n ∈ S.filter (fun n => ¬ g n < k + δ), ee (F n)‖ := norm_add_le _ _
      _ ≤ (2 * δ / lam + 1) + (1 + 1 / δ) := add_le_add hbad hgood
      _ = 2 * δ / lam + 2 + 1 / δ := by ring
  refine (norm_sum_le _ _).trans ((sum_le_sum hclass).trans ?_)
  rw [sum_const, nsmul_eq_mul, Int.card_Icc]
  have hκ1 : ((κ N₂ : ℤ) : ℝ) ≤ g N₂ + δ := Int.floor_le _
  have hκ2 : g N₁ + δ - 1 < ((κ N₁ : ℤ) : ℝ) := Int.sub_one_lt_floor _
  have h0 : 0 ≤ κ N₂ + 1 - κ N₁ := by have := hκmono N₁ N₂ le_rfl hN le_rfl; omega
  have hcard : ((κ N₂ + 1 - κ N₁).toNat : ℝ) ≤ g N₂ - g N₁ + 2 := by
    have e : ((κ N₂ + 1 - κ N₁).toNat : ℝ) = ((κ N₂ + 1 - κ N₁ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    rw [e]; push_cast; linarith
  have hpos : 0 ≤ 2 * δ / lam + 2 + 1 / δ := by positivity
  exact mul_le_mul_of_nonneg_right hcard hpos

end Kerr.PowerfulNumbers
