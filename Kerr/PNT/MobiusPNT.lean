/-
Kerr/PNT/MobiusPNT.lean — new file (written for this repo, not copied).
Assembly of the Möbius prime number theorem with the de la Vallée-Poussin error term:
  ∑_{n ≤ x} μ(n) = O(x · exp(-c √log x)).
Inputs: the smoothed Perron identity (MobiusPerron), the conditional contour estimate
(MobiusContour), and the 1/ζ region bound (MobiusInvZeta), which rest on copied
PrimeNumberTheoremAnd results (Apache-2.0, © the PrimeNumberTheoremAnd contributors).
-/
import Kerr.PNT.MobiusContour

open Complex Filter Topology Set MeasureTheory ArithmeticFunction Asymptotics
open scoped ArithmeticFunction.Moebius ComplexOrder

namespace KerrPNT.Mobius

local notation "ζ" => riemannZeta

/-- On `Re s = σ ∈ (1,2]`, `‖1/ζ(s)‖ ≤ c/(σ-1)`. -/
lemma invZeta_norm_le_line : ∃ c > 0, ∀ σ ∈ Ioc (1 : ℝ) 2, ∀ t : ℝ,
    ‖invZeta (σ + t * I)‖ ≤ c / (σ - 1) := by
  obtain ⟨c, hc, h⟩ := ZetaNear1BndExact
  refine ⟨c, hc, fun σ hσ t ↦ ?_⟩
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ.1
  have hσr : 1 < (σ : ℂ).re := by simpa using hσ.1
  rw [invZeta_eq_LSeries hs, LSeries]
  have h1 : Summable fun n ↦ ‖LSeries.term 1 (σ : ℂ) n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_one_iff.mpr hσr)
  have hle : ∀ n, ‖LSeries.term (fun n ↦ (μ n : ℂ)) ((σ : ℂ) + t * I) n‖ ≤
      ‖LSeries.term 1 (σ : ℂ) n‖ := by
    intro n
    calc _ ≤ ‖LSeries.term (fun n ↦ (μ n : ℂ)) (σ : ℂ) n‖ :=
          (LSeries.norm_term_le_of_re_le_re _ (by simp) n)
      _ ≤ _ := LSeries.norm_term_le _ (by
          simp only [Pi.one_apply, norm_one, Complex.norm_intCast]
          exact_mod_cast abs_moebius_le_one)
  have h2 : Summable fun n ↦ ‖LSeries.term (fun n ↦ (μ n : ℂ)) ((σ : ℂ) + t * I) n‖ :=
    h1.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  have hre : ∀ n, ‖LSeries.term 1 (σ : ℂ) n‖ = (LSeries.term 1 (σ : ℂ) n).re := by
    intro n
    have := LSeries.term_nonneg (a := 1) (n := n) (by simp only [Pi.one_apply]; exact zero_le_one) σ
    rw [Complex.nonneg_iff] at this
    rw [← Complex.re_add_im (LSeries.term 1 (σ : ℂ) n), ← this.2]
    simp [abs_of_nonneg this.1]
  calc ‖∑' n, LSeries.term (fun n ↦ (μ n : ℂ)) ((σ : ℂ) + t * I) n‖
      ≤ ∑' n, ‖LSeries.term (fun n ↦ (μ n : ℂ)) ((σ : ℂ) + t * I) n‖ := norm_tsum_le_tsum_norm h2
    _ ≤ ∑' n, ‖LSeries.term 1 (σ : ℂ) n‖ := h2.tsum_le_tsum hle h1
    _ = (∑' n, LSeries.term 1 (σ : ℂ) n).re := by
        rw [Complex.re_tsum (LSeriesSummable_one_iff.mpr hσr)]
        exact tsum_congr hre
    _ = (ζ σ).re := by rw [← LSeries_one_eq_riemannZeta hσr, LSeries]
    _ ≤ ‖ζ σ‖ := re_le_norm _
    _ ≤ c / (σ - 1) := h σ hσ

/-- The smoothed Möbius sum `S(x) = ∑_{n ≤ x} μ(n) (x - n)`. -/
noncomputable def S (x : ℝ) : ℝ := ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ) * (x - n)

lemma integrable_line {x b : ℝ} (hx : 0 < x) (hb : 1 < b) (hb2 : b ≤ 2) :
    Integrable (fun t : ℝ ↦ Perron.f x (b + t * I) * invZeta (b + t * I)) := by
  obtain ⟨c, hc, hline⟩ := invZeta_norm_le_line
  have hcont : Continuous (fun t : ℝ ↦ Perron.f x (b + t * I) * invZeta (b + t * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hs : 1 < ((b : ℂ) + t * I).re := by simpa using hb
    have hζ : ζ (b + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    have h0 : ((b : ℂ) + t * I) ∈ ({0, -1} : Set ℂ)ᶜ := by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro h; have := congrArg Complex.re h; simp at this; linarith
      · intro h; have := congrArg Complex.re h; simp at this; linarith
    have hf : DifferentiableAt ℂ (Perron.f x) (b + t * I) :=
      (Perron.isHolomorphicOn hx).differentiableAt
        ((Set.toFinite ({0, -1} : Set ℂ)).isClosed.isOpen_compl.mem_nhds h0)
    have hl : ContinuousAt (fun t : ℝ ↦ (b : ℂ) + t * I) t := by fun_prop
    exact ContinuousAt.comp (g := fun s ↦ Perron.f x s * invZeta s)
      (hf.mul (invZeta_differentiableAt hζ)).continuousAt hl
  refine Integrable.mono' ((Perron.isIntegrable (σ := b) hx (by linarith) (by linarith)).norm.mul_const
    (c / (b - 1))) hcont.aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hline b ⟨hb, hb2⟩ t) (norm_nonneg _)

lemma abs_S_eq {x b : ℝ} (hx : 0 < x) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) (hb : 1 < b) :
    2 * Real.pi * |S x| = x * ‖VerticalIntegral (fun s ↦ Perron.f x s * invZeta s) b‖ := by
  rw [perron_moebius hx hxn hb]
  have hsum : (∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℂ) * (1 - n / x)) = ((S x / x : ℝ) : ℂ) := by
    rw [S, Finset.sum_div]
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    field_simp
  rw [hsum]
  simp only [norm_mul, Complex.norm_real, norm_I, Real.norm_eq_abs, abs_div, abs_of_pos hx,
    Complex.norm_ofNat, abs_of_pos Real.pi_pos, mul_one]
  field_simp

/-- **Smoothed bound**: `|S(x)| ≤ K x² exp(-c √log x)` for large non-integral `x`. -/
theorem S_bound : ∃ K > 0, ∃ c > 0, ∃ X₀ ≥ (3 : ℝ), ∀ x ≥ X₀, (∀ n : ℕ, (n : ℝ) ≠ x) →
    |S x| ≤ K * x ^ 2 * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨η, hη, B, hB, T₀, hT₀, hrect⟩ := invZeta_rect
  obtain ⟨c₀, hc₀, hline⟩ := invZeta_norm_le_line
  set lam := Real.sqrt η / 2 with hlam
  have hlam0 : 0 < lam := by positivity
  have hηl : η = 4 * lam ^ 2 := by
    rw [hlam, div_pow, Real.sq_sqrt hη.le]; ring
  set K₁ := 8 / 3 * B + 4 * B * Real.exp 1 + 16 * c₀ * Real.exp 1 / lam ^ 2 with hK₁
  have hK₁pos : 0 < K₁ := by positivity
  refine ⟨K₁, hK₁pos, lam / 2, by positivity,
    max 3 (Real.exp ((Real.log T₀ / lam) ^ 2)), le_max_left _ _, ?_⟩
  intro x hx hxn
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  set L := Real.log x with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hx0]; linarith [Real.exp_one_lt_d9]
  have hL0 : 0 < L := by linarith
  set u := Real.sqrt L with hu
  have hu2 : u ^ 2 = L := Real.sq_sqrt hL0.le
  have hu0 : 0 < u := Real.sqrt_pos.mpr hL0
  set T := Real.exp (lam * u) with hT
  have hT0 : 0 < T := Real.exp_pos _
  have hlogT : Real.log T = lam * u := Real.log_exp _
  have hTT₀ : T₀ ≤ T := by
    have h1 : Real.exp ((Real.log T₀ / lam) ^ 2) ≤ x := (le_max_right _ _).trans hx
    have h2 : (Real.log T₀ / lam) ^ 2 ≤ L := by
      rw [hLdef, Real.le_log_iff_exp_le hx0]; exact h1
    have h3 : Real.log T₀ / lam ≤ u := by
      rw [hu]; exact Real.le_sqrt_of_sq_le h2
    have h4 : Real.log T₀ ≤ lam * u := by
      rw [div_le_iff₀ hlam0] at h3; linarith
    calc T₀ = Real.exp (Real.log T₀) := (Real.exp_log (by linarith)).symm
      _ ≤ T := Real.exp_le_exp.mpr h4
  obtain ⟨hσhalf, hR⟩ := hrect T hTT₀
  set σ₀ := 1 - η / Real.log T with hσ₀
  set b := 1 + 1 / L with hb
  have hb1 : 1 < b := by have : 0 < 1 / L := by positivity
                         linarith
  have hb2 : b ≤ 2 := by
    have : 1 / L ≤ 1 := by rw [div_le_one hL0]; exact hL1
    linarith
  have hσ₀1 : σ₀ < 1 := by
    have : 0 < η / Real.log T := by rw [hlogT]; positivity
    linarith
  have hcont := contour_bound (G := invZeta) (x := x) (b := b) (σ₀ := σ₀) (T := T)
    (B := B * T) (Bb := c₀ * L) hx1 hσhalf (by linarith) hT0
    (fun σ hσ t ht ↦ invZeta_differentiableAt
      (hR σ ⟨hσ.1, hσ.2.trans hb2⟩ t (abs_le.mpr ⟨ht.1, ht.2⟩)).1)
    (fun σ hσ t ht ↦ (hR σ ⟨hσ.1, hσ.2.trans hb2⟩ t (abs_le.mpr ⟨ht.1, ht.2⟩)).2)
    (fun t ↦ by
      have := hline b ⟨hb1, hb2⟩ t
      rwa [show b - 1 = 1 / L by rw [hb]; ring, div_div_eq_mul_div, div_one] at this)
    (integrable_line hx0 hb1 hb2)
  -- evaluate the powers of x
  have hxb : x ^ b = Real.exp 1 * x := by
    rw [Real.rpow_def_of_pos hx0, hb, ← hLdef, mul_add, mul_one, mul_one_div_cancel hL0.ne',
      Real.exp_add, Real.exp_log hx0, mul_comm]
  have hxσ : x ^ σ₀ = x * Real.exp (-(4 * lam * u)) := by
    rw [Real.rpow_def_of_pos hx0, ← hLdef, hσ₀, hlogT, hηl, mul_sub, mul_one, Real.exp_sub,
      Real.exp_log hx0, div_eq_mul_inv, Real.exp_neg]
    congr 2
    rw [← hu2]; field_simp
  have hT2 : T * T = Real.exp (2 * lam * u) := by rw [hT, ← Real.exp_add]; ring_nf
  have hTinv : 1 / T = Real.exp (-(lam * u)) := by rw [hT, Real.exp_neg, one_div]
  -- the log factor
  have hLexp : L ≤ 8 / lam ^ 2 * Real.exp (lam * u / 2) := by
    have h := Real.pow_div_factorial_le_exp (x := lam * u / 2) (by positivity) 2
    simp only [Nat.factorial] at h
    rw [← hu2]
    have : u ^ 2 = 8 / lam ^ 2 * ((lam * u / 2) ^ 2 / 2) := by field_simp; ring
    rw [this]
    gcongr
    simpa using h
  have hbσ : b - σ₀ ≤ 2 := by linarith
  set E := Real.exp (-(lam / 2 * u)) with hE
  have e1 : Real.exp (-(4 * lam * u)) * Real.exp (2 * lam * u) ≤ E := by
    rw [← Real.exp_add, hE]; apply Real.exp_le_exp.mpr; nlinarith
  have e2 : Real.exp (-(lam * u)) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr; nlinarith
  have e3 : Real.exp (lam * u / 2) * Real.exp (-(lam * u)) = E := by
    rw [← Real.exp_add, hE]; ring_nf
  have hE0 : 0 < E := Real.exp_pos _
  have hVI : ‖VerticalIntegral (fun s ↦ Perron.f x s * invZeta s) b‖ ≤ K₁ * x * E := by
    refine hcont.trans ?_
    have t1 : 8 / 3 * (B * T) * x ^ σ₀ * T ≤ 8 / 3 * B * x * E := by
      rw [hxσ]
      calc 8 / 3 * (B * T) * (x * Real.exp (-(4 * lam * u))) * T
          = 8 / 3 * B * x * (Real.exp (-(4 * lam * u)) * (T * T)) := by ring
        _ ≤ 8 / 3 * B * x * E := by rw [hT2]; gcongr
    have t2 : 2 * (b - σ₀) * (B * T) * x ^ b / T ^ 2 ≤ 4 * B * Real.exp 1 * x * E := by
      rw [hxb]
      calc 2 * (b - σ₀) * (B * T) * (Real.exp 1 * x) / T ^ 2
          = 2 * (b - σ₀) * B * Real.exp 1 * x * (1 / T) := by field_simp
        _ ≤ 2 * 2 * B * Real.exp 1 * x * E := by
          rw [hTinv]; gcongr
        _ = 4 * B * Real.exp 1 * x * E := by ring
    have t3 : 2 * (c₀ * L) * x ^ b / T ≤ 16 * c₀ * Real.exp 1 / lam ^ 2 * x * E := by
      rw [hxb]
      calc 2 * (c₀ * L) * (Real.exp 1 * x) / T = 2 * c₀ * Real.exp 1 * x * L * (1 / T) := by
            ring
        _ ≤ 2 * c₀ * Real.exp 1 * x * (8 / lam ^ 2 * Real.exp (lam * u / 2)) *
              Real.exp (-(lam * u)) := by
            rw [hTinv]; gcongr
        _ = 16 * c₀ * Real.exp 1 / lam ^ 2 * x * E := by rw [← e3]; ring
    have : K₁ * x * E = 8 / 3 * B * x * E + 4 * B * Real.exp 1 * x * E +
        16 * c₀ * Real.exp 1 / lam ^ 2 * x * E := by rw [hK₁]; ring
    linarith
  have hS := abs_S_eq hx0 hxn hb1
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hSnn : 0 ≤ |S x| := abs_nonneg _
  have : 2 * Real.pi * |S x| ≤ K₁ * x ^ 2 * E := by
    rw [hS]
    calc x * ‖VerticalIntegral (fun s ↦ Perron.f x s * invZeta s) b‖ ≤ x * (K₁ * x * E) := by
          gcongr
      _ = K₁ * x ^ 2 * E := by ring
  have hEeq : E = Real.exp (-(lam / 2) * Real.sqrt (Real.log x)) := by
    rw [hE, hu, hLdef]; ring_nf
  rw [← hEeq]
  exact le_trans (le_mul_of_one_le_left hSnn hpi) this

/-- Unsmoothing identity: differences of `S` recover the Mertens sum up to `h²`. -/
lemma S_diff (N h : ℕ) :
    |S (N + 1 / 2 + h) - S (N + 1 / 2) - h * ∑ n ∈ Finset.Iic N, (μ n : ℝ)| ≤ (h : ℝ) ^ 2 := by
  have hf1 : ⌊(N : ℝ) + 1 / 2⌋₊ = N := by
    rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
  have hf2 : ⌊(N : ℝ) + 1 / 2 + h⌋₊ = N + h := by
    rw [Nat.floor_eq_iff (by positivity)]; push_cast; constructor <;> linarith
  have hsplit : Finset.Iic (N + h) = Finset.Iic N ∪ Finset.Ioc N (N + h) := by
    ext n; simp only [Finset.mem_Iic, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Iic N) (Finset.Ioc N (N + h)) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Iic, Finset.mem_Ioc] at h1 h2; omega
  rw [S, S, hf1, hf2, hsplit, Finset.sum_union hdisj, Finset.mul_sum]
  have e : ∑ n ∈ Finset.Iic N, (μ n : ℝ) * ((N : ℝ) + 1 / 2 + h - n) -
      ∑ n ∈ Finset.Iic N, (μ n : ℝ) * ((N : ℝ) + 1 / 2 - n) -
      ∑ n ∈ Finset.Iic N, (h : ℝ) * μ n = 0 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero; intro n _; ring
  have : ∑ n ∈ Finset.Iic N, (μ n : ℝ) * ((N : ℝ) + 1 / 2 + h - n) +
      ∑ n ∈ Finset.Ioc N (N + h), (μ n : ℝ) * ((N : ℝ) + 1 / 2 + h - n) -
      ∑ n ∈ Finset.Iic N, (μ n : ℝ) * ((N : ℝ) + 1 / 2 - n) -
      ∑ n ∈ Finset.Iic N, (h : ℝ) * μ n =
      ∑ n ∈ Finset.Ioc N (N + h), (μ n : ℝ) * ((N : ℝ) + 1 / 2 + h - n) := by linarith
  rw [this]
  calc |∑ n ∈ Finset.Ioc N (N + h), (μ n : ℝ) * ((N : ℝ) + 1 / 2 + h - n)|
      ≤ ∑ n ∈ Finset.Ioc N (N + h), |(μ n : ℝ) * ((N : ℝ) + 1 / 2 + h - n)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Ioc N (N + h), (h : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [Finset.mem_Ioc] at hn
        have h1 : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
        have h2 : (n : ℝ) ≤ N + h := by exact_mod_cast hn.2
        rw [abs_mul]
        have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        have hb : |(N : ℝ) + 1 / 2 + h - n| ≤ h := by
          rw [abs_le]; constructor <;> linarith
        calc |(μ n : ℝ)| * |(N : ℝ) + 1 / 2 + h - n| ≤ 1 * h :=
              mul_le_mul hμ hb (abs_nonneg _) zero_le_one
          _ = h := one_mul _
    _ = (h : ℝ) ^ 2 := by simp; ring

lemma sqrt_log_le {x : ℝ} (hx : 2 ≤ x) :
    Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log (x / 2)) + 1 := by
  have h0 : 0 ≤ Real.log (x / 2) := Real.log_nonneg (by linarith)
  have h1 : Real.log x ≤ Real.log (x / 2) + 1 := by
    rw [Real.log_div (by linarith) (by norm_num)]
    linarith [Real.log_two_lt_d9]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have := Real.sq_sqrt h0
  nlinarith [Real.sqrt_nonneg (Real.log (x / 2))]

/-- **Target 4 (core form).** -/
theorem mobius_pnt_error :
    ∃ c > 0, (fun x : ℝ ↦ ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ)) =O[atTop]
      (fun x ↦ x * Real.exp (-c * Real.sqrt (Real.log x))) := by
  obtain ⟨K, hK, c, hc, X₀, hX₀, hS⟩ := S_bound
  set c' := c / 2 with hc'
  have hc'0 : 0 < c' := by positivity
  refine ⟨c', hc'0, ?_⟩
  set K' := 18 * K * Real.exp c + 2 with hK'
  apply IsBigO.of_bound K'
  filter_upwards [eventually_ge_atTop (X₀ + 1), eventually_ge_atTop (Real.exp (c' ^ 2))]
    with x hx1 hx2
  have hx3 : 3 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  set E := Real.exp (-c' * Real.sqrt (Real.log x)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE2 : Real.exp (-c * Real.sqrt (Real.log x)) = E ^ 2 := by
    rw [hE, sq, ← Real.exp_add, hc']; ring_nf
  -- `x E ≥ 1`
  have hxE : 1 ≤ x * E := by
    have hlog : c' ^ 2 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]; exact hx2
    have hsq : c' ≤ Real.sqrt (Real.log x) := Real.le_sqrt_of_sq_le hlog
    have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have : c' * Real.sqrt (Real.log x) ≤ Real.log x := by
      calc c' * Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log x) * Real.sqrt (Real.log x) := by
            gcongr
        _ = Real.log x := Real.mul_self_sqrt hL0
    rw [hE, ← Real.exp_log hx0, ← Real.exp_add, Real.exp_log hx0]
    apply Real.one_le_exp; linarith
  set N := ⌊x⌋₊ with hN
  set h := ⌈x * E⌉₊ with hh
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hhlow : x * E ≤ h := Nat.le_ceil _
  have hhup : (h : ℝ) < x * E + 1 := Nat.ceil_lt_add_one (by positivity)
  have hhpos : (0 : ℝ) < h := by linarith
  have hE1 : E ≤ 1 := by
    rw [hE]; apply Real.exp_le_one_iff.mpr
    have := Real.sqrt_nonneg (Real.log x); nlinarith
  -- bound `|S z|` for the two evaluation points
  have hSz : ∀ z : ℝ, x / 2 ≤ z → z ≤ 3 * x → X₀ ≤ z → (∀ n : ℕ, (n : ℝ) ≠ z) →
      |S z| ≤ 9 * K * Real.exp c * x ^ 2 * E ^ 2 := by
    intro z hz1 hz2 hz3 hzn
    have hz0 : 0 < z := by linarith
    have h1 := hS z hz3 hzn
    have hsq : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log z) + 1 := by
      calc Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log (x / 2)) + 1 := sqrt_log_le (by linarith)
        _ ≤ Real.sqrt (Real.log z) + 1 := by
          gcongr
    have hexp : Real.exp (-c * Real.sqrt (Real.log z)) ≤
        Real.exp c * Real.exp (-c * Real.sqrt (Real.log x)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
    calc |S z| ≤ K * z ^ 2 * Real.exp (-c * Real.sqrt (Real.log z)) := h1
      _ ≤ K * (3 * x) ^ 2 * (Real.exp c * Real.exp (-c * Real.sqrt (Real.log x))) := by
          gcongr
      _ = 9 * K * Real.exp c * x ^ 2 * E ^ 2 := by rw [hE2]; ring
  have hnot : ∀ k : ℕ, ∀ n : ℕ, (n : ℝ) ≠ (N : ℝ) + 1 / 2 + k := by
    intro k n hn
    have : (2 : ℝ) * n = 2 * N + 1 + 2 * k := by linarith
    have : 2 * n = 2 * N + 1 + 2 * k := by exact_mod_cast this
    omega
  have hy1 := hSz ((N : ℝ) + 1 / 2) (by linarith) (by linarith) (by linarith)
    (by simpa using hnot 0)
  have hy2 := hSz ((N : ℝ) + 1 / 2 + h) (by linarith) (by nlinarith) (by linarith) (hnot h)
  have hd := S_diff N h
  -- conclude
  have hM : |(h : ℝ) * ∑ n ∈ Finset.Iic N, (μ n : ℝ)| ≤
      2 * (9 * K * Real.exp c * x ^ 2 * E ^ 2) + (h : ℝ) ^ 2 := by
    set A := S ((N : ℝ) + 1 / 2 + h)
    set B := S ((N : ℝ) + 1 / 2)
    set hMv := (h : ℝ) * ∑ n ∈ Finset.Iic N, (μ n : ℝ)
    have e : hMv = (A - B) - (A - B - hMv) := by ring
    have t1 := abs_sub (A - B) (A - B - hMv)
    have t2 := abs_sub A B
    rw [e]
    linarith
  rw [abs_mul, abs_of_pos hhpos] at hM
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : 0 < x * Real.exp (-c' * Real.sqrt (Real.log x)))]
  rw [← hE]
  have hdiv : |∑ n ∈ Finset.Iic N, (μ n : ℝ)| ≤
      2 * (9 * K * Real.exp c * x ^ 2 * E ^ 2) / h + h := by
    have : |∑ n ∈ Finset.Iic N, (μ n : ℝ)| * h ≤ 2 * (9 * K * Real.exp c * x ^ 2 * E ^ 2) +
        h * h := by nlinarith
    calc |∑ n ∈ Finset.Iic N, (μ n : ℝ)| = |∑ n ∈ Finset.Iic N, (μ n : ℝ)| * h / h := by
          field_simp
      _ ≤ (2 * (9 * K * Real.exp c * x ^ 2 * E ^ 2) + h * h) / h := by gcongr
      _ = _ := by field_simp
  have hfrac : 2 * (9 * K * Real.exp c * x ^ 2 * E ^ 2) / h ≤ 18 * K * Real.exp c * (x * E) := by
    rw [div_le_iff₀ hhpos]
    calc 2 * (9 * K * Real.exp c * x ^ 2 * E ^ 2) = 18 * K * Real.exp c * (x * E) * (x * E) := by
          ring
      _ ≤ 18 * K * Real.exp c * (x * E) * h := by gcongr
  calc |∑ n ∈ Finset.Iic N, (μ n : ℝ)| ≤ 2 * (9 * K * Real.exp c * x ^ 2 * E ^ 2) / h + h := hdiv
    _ ≤ 18 * K * Real.exp c * (x * E) + (x * E + x * E) := by linarith
    _ = K' * (x * E) := by rw [hK']; ring

/-- **Conditional form (any contour shape).** If `ζ` has no zeros on the rectangle
`[σ₀, b] × [-T, T]` and `‖1/ζ‖ ≤ B` there, then the smoothed Mertens sum satisfies an explicit
bound. Combined with `S_diff` this bounds `M(N) = ∑_{n ≤ N} μ(n)`. Here `c₀` is the constant of
`invZeta_norm_le_line` (`‖1/ζ(b+it)‖ ≤ c₀/(b-1)`). -/
theorem S_bound_conditional {x b σ₀ T B : ℝ} (hx : 1 < x) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x)
    (hb : 1 < b) (hb2 : b ≤ 2) (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀b : σ₀ ≤ b) (hT : 0 < T)
    (hzero : ∀ σ ∈ Icc σ₀ b, ∀ t ∈ Icc (-T) T, ζ (σ + t * I) ≠ 0)
    (hB : ∀ σ ∈ Icc σ₀ b, ∀ t ∈ Icc (-T) T, ‖invZeta (σ + t * I)‖ ≤ B) :
    ∃ c₀ > 0, 2 * Real.pi * |S x| ≤ x * (8 / 3 * B * x ^ σ₀ * T +
      2 * (b - σ₀) * B * x ^ b / T ^ 2 + 2 * (c₀ / (b - 1)) * x ^ b / T) := by
  obtain ⟨c₀, hc₀, hline⟩ := invZeta_norm_le_line
  refine ⟨c₀, hc₀, ?_⟩
  rw [abs_S_eq (by linarith) hxn hb]
  gcongr
  exact contour_bound hx hσ₀ hσ₀b hT
    (fun σ hσ t ht ↦ invZeta_differentiableAt (hzero σ hσ t ht)) hB
    (fun t ↦ hline b ⟨hb, hb2⟩ t) (integrable_line (by linarith) hb hb2)

end KerrPNT.Mobius

#print axioms KerrPNT.Mobius.mobius_pnt_error
#print axioms KerrPNT.Mobius.S_bound_conditional
