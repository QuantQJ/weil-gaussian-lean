import Mathlib

/-!
# Perron's formula with the Cesàro kernel, the contour shift, and partial sums

Sections 7–9 of kerr-lean `Kerr/Zeta/Littlewood.lean` (James C. Kerr, Apache-2.0), adapted. Changes from
the source: the kernel is `pk x s = x^s/(s(s+1))` (the source's `Perron.f`); the smoothed Perron identity
`perron_general` is proved here from Mathlib's Mellin inversion (`mellinInv_mellin_eq`, applied to the
Cesàro weight `max (1 − u) 0`, whose Mellin transform is `1/(s(s+1))`), instead of the copied
PrimeNumberTheoremAnd Perron formula, so it needs no condition `x ∉ ℕ`; the contour shift
`vertical_shift` is proved from Mathlib's rectangle Cauchy theorem
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) instead of the copied
PrimeNumberTheoremAnd `verticalIntegral_eq_verticalIntegral`. Integrals are plain `∫ t : ℝ, F(σ + it)`
(the source's `VerticalIntegral` has an extra factor `I`). The kernel, difference and unsmoothing
estimates (`kernel_bound`, `Ssum_diff_bound`, `Ssum_diff`, `partial_sum_bound`) are the source's.

* `perron_general`: for `a 0 = 0`, `‖a n‖ ≤ 1`, `G = L(a, ·)` on `Re s > 1`, `x > 0`, `b > 1`:
  `∫ pk x (b+it) G(b+it) dt = 2π ∑_{n ≤ x} a(n) (1 − n/x)`.
* `vertical_shift`: the line `Re s = 2` may be moved to `Re s = σ₀ ∈ [1/2, 2]` when `G` is holomorphic on
  `Re s ≥ σ₀` with `‖G s‖ ≤ C (1 + |Im s|)^η`, `η < 1`.
* `partial_sum_bound`: if moreover `η = θ/2`, `0 < θ ≤ 1`, then `‖∑_{n ≤ x} a(n)‖ ≤ K x^{σ₀+θ}`, `x ≥ 1`.
-/

noncomputable section
open Complex Set Filter Topology MeasureTheory
open scoped Interval

namespace FleetLandauTransfer

/-- The Perron kernel `x^s/(s(s+1))`. -/
def pk (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s / (s * (s + 1))

/-- The Cesàro weight `max (1 − u) 0`. -/
def cesaro (u : ℝ) : ℂ := ((max (1 - u) 0 : ℝ) : ℂ)

lemma continuous_cesaro : Continuous cesaro := by unfold cesaro; fun_prop

lemma cesaro_eq_indicator {u : ℝ} (hu : 0 < u) :
    cesaro u = indicator (Ioc 0 1) (fun _ => (1 : ℂ)) u
      - indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (1 : ℂ)) u := by
  by_cases h : u ≤ 1
  · have hm : u ∈ Ioc (0 : ℝ) 1 := ⟨hu, h⟩
    rw [indicator_of_mem hm, indicator_of_mem hm, cpow_one, cesaro, max_eq_left (by linarith)]
    push_cast; ring
  · have hm : u ∉ Ioc (0 : ℝ) 1 := fun hm => h hm.2
    rw [indicator_of_notMem hm, indicator_of_notMem hm, cesaro, max_eq_right (by linarith)]
    simp

lemma ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := by
  intro h; rw [h] at hs; simp at hs

lemma add_one_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s + 1 ≠ 0 := by
  intro h; have := congrArg re h; simp at this; linarith

/-- The Mellin transform of the Cesàro weight is `1/(s(s+1))` on `Re s > 0`. -/
lemma hasMellin_cesaro {s : ℂ} (hs : 0 < s.re) : HasMellin cesaro s (1 / (s * (s + 1))) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  have h3 := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at h3
  have hs0 := ne_zero_of_re_pos hs
  have hs1 := add_one_ne_zero_of_re_pos hs
  have e : 1 / s - 1 / (s + 1) = 1 / (s * (s + 1)) := by field_simp; ring
  rw [e] at h3
  have heq : EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (indicator (Ioc 0 1) (fun _ => (1 : ℂ)) t
      - indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (1 : ℂ)) t))
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • cesaro t) (Ioi 0) := fun t ht => by
    simp only [cesaro_eq_indicator (mem_Ioi.mp ht)]
  refine ⟨?_, ?_⟩
  · exact h3.1.congr_fun heq measurableSet_Ioi
  · rw [← h3.2]
    exact (setIntegral_congr_fun measurableSet_Ioi heq).symm

lemma one_add_abs_im_le_norm {s : ℂ} (hs : 1 / 2 ≤ s.re) : (1 + |s.im|) / 4 ≤ ‖s‖ := by
  have h1 := re_le_norm s
  have h2 := abs_im_le_norm s
  linarith [abs_nonneg s.im]

lemma one_add_abs_im_le_norm_add_one {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    (1 + |s.im|) / 2 ≤ ‖s + 1‖ := by
  have h1 := re_le_norm (s + 1)
  have h2 := abs_im_le_norm (s + 1)
  simp only [add_re, one_re, add_im, one_im, add_zero] at h1 h2
  linarith [abs_nonneg s.im]

/-- `‖x^s/(s(s+1))‖ ≤ 8 x^σ (1+|t|)^{-2}` for `σ ≥ 1/2`. -/
lemma norm_pk_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖pk x s‖ ≤ 8 * x ^ s.re * (1 + |s.im|) ^ (-2 : ℝ) := by
  have h1 := one_add_abs_im_le_norm hs
  have h2 := one_add_abs_im_le_norm_add_one hs
  have hp : 0 < 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hprod : (1 + |s.im|) ^ 2 / 8 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul]
    have := mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    nlinarith
  simp only [pk, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  rw [Real.rpow_neg hp.le, Real.rpow_two, div_le_iff₀ (lt_of_lt_of_le (by positivity) hprod)]
  have hxs : 0 ≤ x ^ s.re := Real.rpow_nonneg hx.le _
  calc x ^ s.re = 8 * x ^ s.re * ((1 + |s.im|) ^ 2)⁻¹ * ((1 + |s.im|) ^ 2 / 8) := by
        field_simp
    _ ≤ 8 * x ^ s.re * ((1 + |s.im|) ^ 2)⁻¹ * ‖s * (s + 1)‖ := by gcongr

lemma norm_pk {y : ℝ} (hy : 0 < y) (s : ℂ) : ‖pk y s‖ = y ^ s.re * ‖pk 1 s‖ := by
  simp only [pk, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, ofReal_one, one_cpow, norm_one]
  ring

lemma pk_div {x n : ℝ} (hx : 0 < x) (hn : 0 < n) (s : ℂ) :
    pk (x / n) s = pk x s * (n : ℂ) ^ (-s) := by
  simp only [pk]
  rw [ofReal_div, div_cpow_ofReal_nonneg hx.le hn.le, cpow_neg]
  ring

lemma pk_differentiableAt {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (pk x) s := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold pk
  exact (differentiableAt_id.const_cpow (Or.inl hx0)).div
    (differentiableAt_id.mul (differentiableAt_id.add_const 1))
    (mul_ne_zero (ne_zero_of_re_pos hs) (add_one_ne_zero_of_re_pos hs))

lemma continuous_pk_line {x : ℝ} (hx : 0 < x) {b : ℝ} (hb : 0 < b) :
    Continuous fun t : ℝ => pk x (b + t * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have h1 : ContinuousAt (fun t : ℝ => (b : ℂ) + t * I) t := by fun_prop
  exact ContinuousAt.comp (g := pk x) (pk_differentiableAt hx (by simpa using hb)).continuousAt h1

lemma integrable_pk_line {x : ℝ} (hx : 0 < x) {b : ℝ} (hb : 1 / 2 ≤ b) :
    Integrable fun t : ℝ => pk x (b + t * I) := by
  have hmaj : Integrable (fun t : ℝ => 8 * x ^ b * (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (r := 2) (by simp)).const_mul _
  refine Integrable.mono' hmaj (continuous_pk_line hx (by linarith)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have hs : 1 / 2 ≤ ((b : ℂ) + t * I).re := by simpa using hb
  have := norm_pk_le hx hs
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at this
  rw [Real.norm_eq_abs]
  exact this

/-- **Perron's formula for one term** (Mellin inversion of the Cesàro weight): for `y > 0`, `b ≥ 1/2`,
`∫ pk y (b+it) dt = 2π max (1 − 1/y) 0`. -/
theorem integral_pk {y : ℝ} (hy : 0 < y) {b : ℝ} (hb : 1 / 2 ≤ b) :
    ∫ t : ℝ, pk y (b + t * I) = 2 * Real.pi * cesaro (1 / y) := by
  have hb0 : 0 < b := by linarith
  have hre : ∀ t : ℝ, 0 < ((b : ℂ) + t * I).re := fun t => by simpa using hb0
  have hM : ∀ t : ℝ, mellin cesaro (b + t * I) = pk 1 (b + t * I) := fun t => by
    rw [(hasMellin_cesaro (hre t)).2, pk, ofReal_one, one_cpow]
  have hf : MellinConvergent cesaro (b : ℂ) := (hasMellin_cesaro (by simpa using hb0)).1
  have hFf : VerticalIntegrable (mellin cesaro) b := by
    unfold VerticalIntegrable
    simp only [hM]
    exact integrable_pk_line one_pos hb
  have key := mellinInv_mellin_eq b cesaro (x := 1 / y) (by positivity) hf hFf
    continuous_cesaro.continuousAt
  rw [← key, mellinInv]
  have hpt : ∀ t : ℝ, (((1 / y : ℝ)) : ℂ) ^ (-((b : ℂ) + t * I)) • mellin cesaro (b + t * I) =
      pk y (b + t * I) := by
    intro t
    rw [hM, smul_eq_mul, pk, pk, ofReal_one, one_cpow, one_div, ofReal_inv,
      inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hy.le]; exact Real.pi_pos.ne), cpow_neg, inv_inv]
    ring
  simp only [hpt]
  rw [Complex.real_smul, ← mul_assoc]
  have h2pi : (2 * Real.pi : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast; field_simp
  rw [h2pi, one_mul]

lemma cesaro_div {x : ℝ} (hx : 0 < x) {n : ℕ} :
    cesaro (n / x) = if (n : ℝ) ≤ x then 1 - (n : ℂ) / x else 0 := by
  unfold cesaro
  split_ifs with h
  · rw [max_eq_left (by rw [sub_nonneg, div_le_one hx]; exact h)]; push_cast; ring
  · push Not at h
    rw [max_eq_right (by rw [sub_nonpos, le_div_iff₀ hx]; linarith)]; simp

/-- **Smoothed Perron identity**, for any coefficients `a` with `a 0 = 0`, `‖a n‖ ≤ 1`, and any
`G` equal to the `L`-series of `a` on `Re s > 1` (adapted from kerr-lean `perron_general`; the
one-term formula is `integral_pk`). -/
theorem perron_general {a : ℕ → ℂ} (ha0 : a 0 = 0) (ha : ∀ n, ‖a n‖ ≤ 1) {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s) {x b : ℝ} (hx : 0 < x) (hb : 1 < b) :
    ∫ t : ℝ, pk x (b + t * I) * G (b + t * I) =
      2 * Real.pi * ∑ n ∈ Finset.Iic ⌊x⌋₊, a n * (1 - n / x) := by
  set g : ℕ → ℝ → ℂ := fun n t ↦
    if n = 0 then 0 else a n * pk (x / n) (b + t * I) with hg
  have hb2 : 1 / 2 ≤ b := by linarith
  -- pointwise expansion
  have hpt : ∀ t : ℝ, pk x (b + t * I) * G (b + t * I) = ∑' n, g n t := by
    intro t
    have hre : 1 < ((b : ℂ) + t * I).re := by simpa using hb
    rw [hG _ hre, LSeries, ← tsum_mul_left]
    congr 1; funext n
    rw [LSeries.term_def]
    by_cases hn : n = 0
    · simp [hg, hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [hg, hn, ite_false]
      rw [pk_div hx hnpos, div_eq_mul_inv, ← cpow_neg]
      push_cast
      ring
  -- integrability of each term
  have hint : ∀ n, Integrable (g n) := by
    intro n
    by_cases hn : n = 0
    · simp [hg, hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [hg, hn, ite_false]
      exact (integrable_pk_line (div_pos hx hnpos) hb2).const_mul _
  set K : ℝ := ∫ t : ℝ, ‖pk 1 (b + t * I)‖ with hK
  have hK1 : Integrable (fun t : ℝ ↦ ‖pk 1 (b + t * I)‖) :=
    (integrable_pk_line one_pos hb2).norm
  have hbound : ∀ n, ∫ t, ‖g n t‖ ≤ x ^ b * K * (n : ℝ) ^ (-b) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [hg, Real.zero_rpow (by linarith : -b ≠ 0)]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have e : ∀ t : ℝ, ‖g n t‖ ≤ x ^ b * (n : ℝ) ^ (-b) * ‖pk 1 (b + t * I)‖ := by
        intro t
        simp only [hg, hn, ite_false, norm_mul]
        rw [norm_pk (div_pos hx hnpos)]
        have hμ : ‖a n‖ ≤ 1 := ha n
        have hre : ((b : ℂ) + t * I).re = b := by simp
        rw [hre, Real.div_rpow hx.le hnpos.le, div_eq_mul_inv, ← Real.rpow_neg hnpos.le]
        calc ‖a n‖ * (x ^ b * (n : ℝ) ^ (-b) * ‖pk 1 (b + t * I)‖)
            ≤ 1 * (x ^ b * (n : ℝ) ^ (-b) * ‖pk 1 (b + t * I)‖) := by gcongr
          _ = _ := one_mul _
      calc ∫ t, ‖g n t‖ ≤ ∫ t : ℝ, x ^ b * (n : ℝ) ^ (-b) * ‖pk 1 (b + t * I)‖ :=
            integral_mono (hint n).norm (hK1.const_mul _) e
        _ = x ^ b * K * (n : ℝ) ^ (-b) := by rw [integral_const_mul]; ring
  have hsum : Summable fun n ↦ ∫ t, ‖g n t‖ := by
    refine Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) hbound ?_
    exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  -- swap
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hterm : ∀ n, ∫ t, g n t =
      2 * Real.pi * (a n * (if (n : ℝ) ≤ x then 1 - (n : ℂ) / x else 0)) := by
    intro n
    by_cases hn : n = 0
    · simp [hg, hn, ha0]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [hg, hn, ite_false, integral_const_mul]
      rw [integral_pk (div_pos hx hnpos) hb2, one_div_div, cesaro_div hx]
      ring
  calc ∫ t : ℝ, pk x (b + t * I) * G (b + t * I)
      = ∫ t : ℝ, ∑' n, g n t := integral_congr_ae (Eventually.of_forall hpt)
    _ = ∑' n, ∫ t, g n t := hswap.symm
    _ = ∑' n, 2 * Real.pi * (a n * (if (n : ℝ) ≤ x then 1 - (n : ℂ) / x else 0)) := by
        congr 1; funext n; exact hterm n
    _ = ∑ n ∈ Finset.Iic ⌊x⌋₊,
          2 * Real.pi * (a n * (if (n : ℝ) ≤ x then 1 - (n : ℂ) / x else 0)) := by
        apply tsum_eq_sum
        intro n hn
        rw [Finset.mem_Iic, Nat.le_floor_iff hx.le] at hn
        rw [ite_eq_right hn]; ring
    _ = 2 * Real.pi * ∑ n ∈ Finset.Iic ⌊x⌋₊, a n * (1 - n / x) := by
        rw [← Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_Iic, Nat.le_floor_iff hx.le] at hn
        rw [ite_eq_left hn]

lemma norm_pk_mul_le {x C η : ℝ} (hx : 0 < x) {G : ℂ → ℂ} {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (hG : ‖G s‖ ≤ C * (1 + |s.im|) ^ η) :
    ‖pk x s * G s‖ ≤ 8 * C * x ^ s.re * (1 + |s.im|) ^ (η - 2) := by
  have hp : 0 < 1 + |s.im| := by linarith [abs_nonneg s.im]
  rw [norm_mul]
  have hC : 0 ≤ C * (1 + |s.im|) ^ η := (norm_nonneg _).trans hG
  calc ‖pk x s‖ * ‖G s‖ ≤ (8 * x ^ s.re * (1 + |s.im|) ^ (-2 : ℝ)) *
        (C * (1 + |s.im|) ^ η) := mul_le_mul (norm_pk_le hx hs) hG (norm_nonneg _)
          (by positivity)
    _ = 8 * C * x ^ s.re * ((1 + |s.im|) ^ (-2 : ℝ) * (1 + |s.im|) ^ η) := by ring
    _ = 8 * C * x ^ s.re * (1 + |s.im|) ^ (η - 2) := by
        rw [← Real.rpow_add hp]; ring_nf

lemma integrable_pk_mul_line {G : ℂ → ℂ} {σ C η x : ℝ} (hσ : 1 / 2 ≤ σ) (hη : η < 1)
    (hx : 0 < x)
    (hcont : Continuous fun y : ℝ => G (σ + y * I))
    (hGb : ∀ y : ℝ, ‖G (σ + y * I)‖ ≤ C * (1 + |y|) ^ η) :
    Integrable (fun y : ℝ => pk x (σ + y * I) * G (σ + y * I)) := by
  have hmaj : Integrable (fun y : ℝ => 8 * C * x ^ σ * (1 + ‖y‖) ^ (-(2 - η))) :=
    (integrable_one_add_norm (E := ℝ) (r := 2 - η) (by simp; linarith)).const_mul _
  have hcontF : Continuous fun y : ℝ => pk x (σ + y * I) * G (σ + y * I) := by
    refine Continuous.mul ?_ hcont
    rw [continuous_iff_continuousAt]
    intro y
    have h1 : ContinuousAt (fun y : ℝ => (σ : ℂ) + y * I) y := by fun_prop
    exact ContinuousAt.comp (g := pk x)
      (pk_differentiableAt hx (by simp; linarith)).continuousAt h1
  refine Integrable.mono' hmaj hcontF.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hs : 1 / 2 ≤ ((σ : ℂ) + y * I).re := by simpa using hσ
  have := norm_pk_mul_le hx hs (G := G) (C := C) (η := η) (by simpa using hGb y)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at this
  rw [Real.norm_eq_abs, show -(2 - η) = η - 2 by ring]
  exact this


/-- **Contour shift** `∫_{(2)} = ∫_{(σ₀)}` for `pk x s · G(s)`, when `G` is holomorphic on
`Re s ≥ σ₀ ∈ [1/2, 2]` with `‖G(s)‖ ≤ C (1+|Im s|)^η`, `η < 1` (Mathlib's rectangle Cauchy theorem,
horizontal sides `→ 0`; the horizontal estimate is the source's). -/
theorem vertical_shift {G : ℂ → ℂ} {σ₀ C η x : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀2 : σ₀ ≤ 2)
    (hη : η < 1) (hx : 1 ≤ x) (hC : 0 ≤ C)
    (hGd : ∀ s : ℂ, σ₀ ≤ s.re → DifferentiableAt ℂ G s)
    (hGb : ∀ s : ℂ, σ₀ ≤ s.re → ‖G s‖ ≤ C * (1 + |s.im|) ^ η) :
    (∫ t : ℝ, pk x (σ₀ + t * I) * G (σ₀ + t * I)) =
      ∫ t : ℝ, pk x ((2 : ℝ) + t * I) * G ((2 : ℝ) + t * I) := by
  have hx0 : 0 < x := by linarith
  set f : ℂ → ℂ := fun s => pk x s * G s with hf
  have hlineG : ∀ σ, σ₀ ≤ σ → Continuous fun y : ℝ => G (σ + y * I) := by
    intro σ hσ
    rw [continuous_iff_continuousAt]
    intro y
    have h1 : ContinuousAt (fun y : ℝ => (σ : ℂ) + y * I) y := by fun_prop
    exact ContinuousAt.comp (g := G) (hGd _ (by simpa using hσ)).continuousAt h1
  have hlineB : ∀ σ, σ₀ ≤ σ → ∀ y : ℝ, ‖G (σ + y * I)‖ ≤ C * (1 + |y|) ^ η := by
    intro σ hσ y
    have := hGb ((σ : ℂ) + y * I) (by simpa using hσ)
    simpa using this
  -- horizontal integrals
  have hhor : ∀ y : ℝ, ‖∫ u in σ₀..2, f (u + y * I)‖ ≤
      (2 - σ₀) * (8 * C * x ^ (2 : ℝ)) * (1 + |y|) ^ (η - 2) := by
    intro y
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ₀) (b := 2)
      (C := 8 * C * x ^ (2 : ℝ) * (1 + |y|) ^ (η - 2))
      (f := fun u : ℝ => f (u + y * I)) (by
        intro u hu
        rw [uIoc_of_le hσ₀2] at hu
        have hs : 1 / 2 ≤ ((u : ℂ) + y * I).re := by simp; linarith [hu.1]
        have h1 := norm_pk_mul_le hx0 hs (hGb _ (by simp; linarith [hu.1]))
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, add_im, mul_im, zero_add] at h1
        refine h1.trans ?_
        have hxu : x ^ u ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hu.2
        have hp : 0 ≤ (1 + |y|) ^ (η - 2) := Real.rpow_nonneg (by positivity) _
        have hC8 : 0 ≤ 8 * C := by positivity
        gcongr)
    calc _ ≤ 8 * C * x ^ (2 : ℝ) * (1 + |y|) ^ (η - 2) * |2 - σ₀| := this
      _ = _ := by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - σ₀)]; ring
  have hdecay : Tendsto (fun y : ℝ => (2 - σ₀) * (8 * C * x ^ (2 : ℝ)) * (1 + |y|) ^ (η - 2))
      (atTop ⊔ atBot) (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => 1 + |y|) (atTop ⊔ atBot) atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_abs_atTop_atTop.sup tendsto_abs_atBot_atTop)
    have h2 := (tendsto_rpow_neg_atTop (y := 2 - η) (by linarith)).comp h1
    have h3 := h2.const_mul ((2 - σ₀) * (8 * C * x ^ (2 : ℝ)))
    rw [mul_zero] at h3
    refine h3.congr fun y => ?_
    simp only [Function.comp, neg_sub]
  have hT := squeeze_zero_norm hhor hdecay
  have htop : Tendsto (fun T : ℝ => ∫ u in σ₀..2, f (u + T * I)) atTop (𝓝 0) :=
    hT.mono_left le_sup_left
  have hbot : Tendsto (fun T : ℝ => ∫ u in σ₀..2, f (u + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0) :=
    (hT.mono_left le_sup_right).comp tendsto_neg_atTop_atBot
  have h2 := integrable_pk_mul_line (by norm_num) hη hx0 (hlineG 2 hσ₀2) (hlineB 2 hσ₀2)
  have h1 := integrable_pk_mul_line hσ₀ hη hx0 (hlineG σ₀ le_rfl) (hlineB σ₀ le_rfl)
  have hV2 := intervalIntegral_tendsto_integral h2 tendsto_neg_atTop_atBot tendsto_id
  have hV1 := intervalIntegral_tendsto_integral h1 tendsto_neg_atTop_atBot tendsto_id
  set R : ℝ → ℂ := fun T => (∫ u in σ₀..2, f (u + ((-T : ℝ) : ℂ) * I)) - (∫ u in σ₀..2, f (u + T * I))
      + I * (∫ y in (-T)..id T, f ((2 : ℝ) + y * I)) - I * (∫ y in (-T)..id T, f (σ₀ + y * I)) with hR
  have hlim : Tendsto R atTop (𝓝 (0 - 0 + I * (∫ y : ℝ, f ((2 : ℝ) + y * I))
        - I * (∫ y : ℝ, f (σ₀ + y * I)))) :=
    ((hbot.sub htop).add (hV2.const_mul I)).sub (hV1.const_mul I)
  have hzero : ∀ T : ℝ, R T = 0 := by
    intro T
    have hd : DifferentiableOn ℂ f ([[((σ₀ : ℂ) + ((-T : ℝ) : ℂ) * I).re, (((2 : ℝ) : ℂ) + T * I).re]] ×ℂ
        [[((σ₀ : ℂ) + ((-T : ℝ) : ℂ) * I).im, (((2 : ℝ) : ℂ) + T * I).im]]) := by
      intro z hz
      rw [mem_reProdIm] at hz
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at hz
      have hzre : σ₀ ≤ z.re := by
        have := hz.1; rw [uIcc_of_le hσ₀2] at this; exact this.1
      exact ((pk_differentiableAt hx0 (by linarith)).mul (hGd z hzre)).differentiableWithinAt
    have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((σ₀ : ℂ) + ((-T : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + T * I) hd
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, smul_eq_mul] at key
    simp only [hR, id]
    rw [← key]
  have heq := tendsto_nhds_unique hlim ((tendsto_const_nhds (x := (0 : ℂ))).congr fun T => (hzero T).symm)
  have hI : I ≠ 0 := I_ne_zero
  have : I * ((∫ y : ℝ, f ((2 : ℝ) + y * I)) - (∫ y : ℝ, f (σ₀ + y * I))) = I * 0 := by
    rw [mul_sub, mul_zero]; linear_combination heq
  have := mul_left_cancel₀ hI this
  simp only [hf] at this
  linear_combination -this

/-- Mean-value bound: `‖y·y^s − x·x^s‖ ≤ ‖s+1‖ · y^σ · (y − x)` for `0 < x ≤ y`, `σ ≥ 0`. -/
lemma norm_mul_cpow_sub_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(y : ℂ) * (y : ℂ) ^ s - (x : ℂ) * (x : ℂ) ^ s‖ ≤ ‖s + 1‖ * y ^ s.re * (y - x) := by
  set f : ℝ → ℂ := fun u => (u : ℂ) * (u : ℂ) ^ s with hf
  have hderiv : ∀ u : ℝ, 0 < u → HasDerivAt f ((s + 1) * (u : ℂ) ^ s) u := by
    intro u hu
    have hslit : (u : ℂ) ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left; simpa using hu
    have h1 : HasDerivAt (fun v : ℝ => (v : ℂ) ^ s) (s * (u : ℂ) ^ (s - 1)) u :=
      (Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt.comp_ofReal
    have h2 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := hasDerivAt_id u |>.ofReal_comp
    have h3 := h2.mul h1
    convert h3 using 1
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
    rw [cpow_sub _ _ hu0, cpow_one]
    field_simp
    ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := x) (b := y)
    (f' := fun u => (s + 1) * (u : ℂ) ^ s) (C := ‖s + 1‖ * y ^ s.re)
    (fun u hu => (hderiv u (by linarith [hu.1])).hasDerivWithinAt)
    (fun u hu => by
      have hu0 : 0 < u := by linarith [hu.1]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      gcongr
      exact hu.2.le) y ⟨hxy, le_rfl⟩
  simpa [hf] using hmv

lemma perron_mul_sub_eq {x y : ℝ} {s : ℂ} :
    (y : ℂ) * pk y s - (x : ℂ) * pk x s =
      ((y : ℂ) * (y : ℂ) ^ s - (x : ℂ) * (x : ℂ) ^ s) / (s * (s + 1)) := by
  simp only [pk]; ring

/-- `p ≤ Q u w^{-2}` and `p ≤ Q v w^{-1}` give `p ≤ Q u^θ v^{1−θ} w^{−(1+θ)}`. -/
lemma le_interp_of_le_two {p Q u v w θ : ℝ} (hp : 0 ≤ p) (hQ : 0 ≤ Q) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hw : 0 < w) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA : p ≤ Q * u * w ^ (-2 : ℝ)) (hB : p ≤ Q * v * w ^ (-1 : ℝ)) :
    p ≤ Q * u ^ θ * v ^ (1 - θ) * w ^ (-(1 + θ)) := by
  rcases hp.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  have hw2 : 0 < w ^ (-2 : ℝ) := Real.rpow_pos_of_pos hw _
  have hw1 : 0 < w ^ (-1 : ℝ) := Real.rpow_pos_of_pos hw _
  have hQu : 0 < Q * u := by
    by_contra h; push Not at h
    have : Q * u * w ^ (-2 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hw2.le
    linarith
  have hQv : 0 < Q * v := by
    by_contra h; push Not at h
    have : Q * v * w ^ (-1 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hw1.le
    linarith
  have hQ0 : 0 < Q := by
    rcases hQ.eq_or_lt with h | h
    · rw [← h, zero_mul] at hQu; exact absurd hQu (lt_irrefl 0)
    · exact h
  have hu0 : 0 < u := pos_of_mul_pos_right hQu hQ0.le
  have hv0 : 0 < v := pos_of_mul_pos_right hQv hQ0.le
  have hsplit : p = p ^ θ * p ^ (1 - θ) := by
    rw [← Real.rpow_add hpos]; simp
  have h1 : p ^ θ ≤ (Q * u * w ^ (-2 : ℝ)) ^ θ := Real.rpow_le_rpow hp hA hθ0
  have h2 : p ^ (1 - θ) ≤ (Q * v * w ^ (-1 : ℝ)) ^ (1 - θ) :=
    Real.rpow_le_rpow hp hB (by linarith)
  have hprod := mul_le_mul h1 h2 (Real.rpow_nonneg hp _) (Real.rpow_nonneg (by positivity) _)
  rw [← hsplit] at hprod
  refine hprod.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) hw2.le, Real.mul_rpow hQ0.le hu0.le,
    Real.mul_rpow (by positivity) hw1.le, Real.mul_rpow hQ0.le hv0.le,
    ← Real.rpow_mul hw.le, ← Real.rpow_mul hw.le]
  have eQ : Q ^ θ * Q ^ (1 - θ) = Q := by rw [← Real.rpow_add hQ0]; simp
  have ew : w ^ (-2 * θ) * w ^ (-1 * (1 - θ)) = w ^ (-(1 + θ)) := by
    rw [← Real.rpow_add hw]; ring_nf
  calc Q ^ θ * u ^ θ * w ^ (-2 * θ) * (Q ^ (1 - θ) * v ^ (1 - θ) * w ^ (-1 * (1 - θ)))
      = (Q ^ θ * Q ^ (1 - θ)) * u ^ θ * v ^ (1 - θ) * (w ^ (-2 * θ) * w ^ (-1 * (1 - θ))) := by
        ring
    _ = Q * u ^ θ * v ^ (1 - θ) * w ^ (-(1 + θ)) := by rw [eQ, ew]

/-- **Kernel bound**: `‖y f_y(s) − x f_x(s)‖ ≤ 16 y^{σ+θ} (y−x)^{1−θ} (1+|t|)^{−(1+θ)}`. -/
lemma kernel_bound {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {s : ℂ} (hs : 1 / 2 ≤ s.re)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖(y : ℂ) * pk y s - (x : ℂ) * pk x s‖ ≤
      16 * y ^ s.re * y ^ θ * (y - x) ^ (1 - θ) * (1 + |s.im|) ^ (-(1 + θ)) := by
  have hy : 0 < y := hx.trans_le hxy
  set w := 1 + |s.im| with hw
  have hw0 : 0 < w := by rw [hw]; linarith [abs_nonneg s.im]
  have h1 := one_add_abs_im_le_norm hs
  have h2 := one_add_abs_im_le_norm_add_one hs
  have hsn : 0 < ‖s‖ := lt_of_lt_of_le (by positivity) h1
  have hs1n : 0 < ‖s + 1‖ := lt_of_lt_of_le (by positivity) h2
  rw [perron_mul_sub_eq, norm_div, norm_mul]
  set D := ‖(y : ℂ) * (y : ℂ) ^ s - (x : ℂ) * (x : ℂ) ^ s‖ with hD
  -- bound A
  have hDA : D ≤ 2 * y ^ s.re * y := by
    have e1 : ‖(y : ℂ) * (y : ℂ) ^ s‖ = y ^ s.re * y := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy]; ring
    have e2 : ‖(x : ℂ) * (x : ℂ) ^ s‖ = x ^ s.re * x := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx]; ring
    have e3 : x ^ s.re * x ≤ y ^ s.re * y := by
      gcongr
    have := norm_sub_le ((y : ℂ) * (y : ℂ) ^ s) ((x : ℂ) * (x : ℂ) ^ s)
    rw [e1, e2] at this
    linarith
  have hDB := norm_mul_cpow_sub_le hx hxy (s := s) (by linarith)
  have hwm2 : w ^ (-2 : ℝ) = (w ^ 2)⁻¹ := by rw [Real.rpow_neg hw0.le, Real.rpow_two]
  have hwm1 : w ^ (-1 : ℝ) = w⁻¹ := Real.rpow_neg_one w
  have hA : D / (‖s‖ * ‖s + 1‖) ≤ 16 * y ^ s.re * y * w ^ (-2 : ℝ) := by
    rw [hwm2, div_le_iff₀ (by positivity)]
    have hprod : w ^ 2 / 8 ≤ ‖s‖ * ‖s + 1‖ := by
      have := mul_le_mul h1 h2 (by positivity) (norm_nonneg _); nlinarith
    calc D ≤ 2 * y ^ s.re * y := hDA
      _ = 16 * y ^ s.re * y * (w ^ 2)⁻¹ * (w ^ 2 / 8) := by field_simp; ring
      _ ≤ 16 * y ^ s.re * y * (w ^ 2)⁻¹ * (‖s‖ * ‖s + 1‖) := by gcongr
  have hB : D / (‖s‖ * ‖s + 1‖) ≤ 16 * y ^ s.re * (y - x) * w ^ (-1 : ℝ) := by
    rw [hwm1, div_le_iff₀ (by positivity)]
    calc D ≤ ‖s + 1‖ * y ^ s.re * (y - x) := hDB
      _ = 4 * y ^ s.re * (y - x) * w⁻¹ * (w / 4) * ‖s + 1‖ := by field_simp
      _ ≤ 16 * y ^ s.re * (y - x) * w⁻¹ * ‖s‖ * ‖s + 1‖ := by
          have hyx : 0 ≤ y - x := by linarith
          have : 0 ≤ y ^ s.re := Real.rpow_nonneg hy.le _
          gcongr
          norm_num
      _ = 16 * y ^ s.re * (y - x) * w⁻¹ * (‖s‖ * ‖s + 1‖) := by ring
  have key := le_interp_of_le_two (p := D / (‖s‖ * ‖s + 1‖)) (Q := 16 * y ^ s.re) (u := y)
    (v := y - x) (w := w) (θ := θ) (by positivity) (by positivity) hy.le (by linarith) hw0 hθ0 hθ1
    hA hB
  calc D / (‖s‖ * ‖s + 1‖) ≤ 16 * y ^ s.re * y ^ θ * (y - x) ^ (1 - θ) * w ^ (-(1 + θ)) := key
    _ = _ := rfl

/-! ## 9. Smoothed sums and their differences -/

/-- Smoothed partial sum `∑_{n ≤ x} a(n) (x − n)`. -/
def Ssum (a : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Finset.Iic ⌊x⌋₊, a n * ((x : ℂ) - n)

lemma two_pi_Ssum {a : ℕ → ℂ} (ha0 : a 0 = 0) (ha : ∀ n, ‖a n‖ ≤ 1) {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s) {x : ℝ} (hx : 0 < x) :
    2 * Real.pi * Ssum a x = x * ∫ t : ℝ, pk x ((2 : ℝ) + t * I) * G ((2 : ℝ) + t * I) := by
  rw [perron_general ha0 ha hG hx (by norm_num : (1 : ℝ) < 2), Ssum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp

lemma line_continuous {G : ℂ → ℂ} {σ₀ σ : ℝ} (hGd : ∀ s : ℂ, σ₀ ≤ s.re → DifferentiableAt ℂ G s)
    (hσ : σ₀ ≤ σ) : Continuous fun y : ℝ => G (σ + y * I) := by
  rw [continuous_iff_continuousAt]
  intro y
  have h1 : ContinuousAt (fun y : ℝ => (σ : ℂ) + y * I) y := by fun_prop
  exact ContinuousAt.comp (g := G) (hGd _ (by simpa using hσ)).continuousAt h1

lemma line_bound {G : ℂ → ℂ} {σ₀ σ C η : ℝ}
    (hGb : ∀ s : ℂ, σ₀ ≤ s.re → ‖G s‖ ≤ C * (1 + |s.im|) ^ η) (hσ : σ₀ ≤ σ) (y : ℝ) :
    ‖G (σ + y * I)‖ ≤ C * (1 + |y|) ^ η := by
  have := hGb ((σ : ℂ) + y * I) (by simpa using hσ)
  simpa using this

/-- **Difference bound for the smoothed sums.** If `G = L(a, ·)` on `Re s > 1`, `G` is
holomorphic on `Re s ≥ σ₀` with `‖G(s)‖ ≤ C (1+|t|)^{θ/2}` there (`0 < θ ≤ 1`), then for
non-integers `1 ≤ x ≤ y`:
`‖S(y) − S(x)‖ ≤ 16 C I_θ · y^{σ₀+θ} (y−x)^{1−θ}`, `I_θ = ∫ (1+|t|)^{−(1+θ/2)} dt`. -/
theorem Ssum_diff_bound {a : ℕ → ℂ} (ha0 : a 0 = 0) (ha : ∀ n, ‖a n‖ ≤ 1) {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s) {σ₀ θ C : ℝ} (hσ₀ : 1 / 2 ≤ σ₀)
    (hσ₀2 : σ₀ ≤ 2) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C)
    (hGd : ∀ s : ℂ, σ₀ ≤ s.re → DifferentiableAt ℂ G s)
    (hGb : ∀ s : ℂ, σ₀ ≤ s.re → ‖G s‖ ≤ C * (1 + |s.im|) ^ (θ / 2))
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    ‖Ssum a y - Ssum a x‖ ≤
      16 * C * (∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2))) * y ^ (σ₀ + θ) * (y - x) ^ (1 - θ) := by
  have hx0 : 0 < x := by linarith
  have hy1 : 1 ≤ y := hx.trans hxy
  have hy0 : 0 < y := by linarith
  have hη : θ / 2 < 1 := by linarith
  set F : ℝ → ℂ → ℂ := fun z s => pk z s * G s with hF
  have hshift : ∀ z : ℝ, 1 ≤ z → (∫ t : ℝ, F z ((2 : ℝ) + t * I)) = ∫ t : ℝ, F z (σ₀ + t * I) :=
    fun z hz => (vertical_shift hσ₀ hσ₀2 hη hz hC hGd hGb).symm
  have hint : ∀ z : ℝ, 0 < z → Integrable (fun t : ℝ => F z (σ₀ + t * I)) := fun z hz =>
    integrable_pk_mul_line hσ₀ hη hz (line_continuous hGd le_rfl) (line_bound hGb le_rfl)
  have hsx := two_pi_Ssum ha0 ha hG hx0
  have hsy := two_pi_Ssum ha0 ha hG hy0
  have e : 2 * Real.pi * (Ssum a y - Ssum a x) =
      ∫ t : ℝ, ((y : ℂ) * F y (σ₀ + t * I) - (x : ℂ) * F x (σ₀ + t * I)) := by
    rw [mul_sub, hsy, hsx, hshift y hy1, hshift x hx,
      integral_sub ((hint y hy0).const_mul _) ((hint x hx0).const_mul _), integral_const_mul,
      integral_const_mul]
  set K0 := 16 * C * y ^ σ₀ * y ^ θ * (y - x) ^ (1 - θ) with hK0
  have hK0nn : 0 ≤ K0 := by
    have : 0 ≤ (y - x) ^ (1 - θ) := Real.rpow_nonneg (by linarith) _
    positivity
  have hgint : Integrable (fun t : ℝ => K0 * (1 + ‖t‖) ^ (-(1 + θ / 2))) :=
    (integrable_one_add_norm (E := ℝ) (r := 1 + θ / 2) (by simp; linarith)).const_mul _
  have hpt : ∀ t : ℝ, ‖(y : ℂ) * F y (σ₀ + t * I) - (x : ℂ) * F x (σ₀ + t * I)‖ ≤
      K0 * (1 + ‖t‖) ^ (-(1 + θ / 2)) := by
    intro t
    have hs : 1 / 2 ≤ ((σ₀ : ℂ) + t * I).re := by simpa using hσ₀
    have hk := kernel_bound hx0 hxy hs hθ0.le hθ1
    have hG' := line_bound hGb le_rfl t (σ := σ₀)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hk
    have e2 : (y : ℂ) * F y (σ₀ + t * I) - (x : ℂ) * F x (σ₀ + t * I) =
        ((y : ℂ) * pk y (σ₀ + t * I) - (x : ℂ) * pk x (σ₀ + t * I)) *
          G (σ₀ + t * I) := by simp only [hF]; ring
    rw [e2, norm_mul, Real.norm_eq_abs]
    have hw : 0 < 1 + |t| := by linarith [abs_nonneg t]
    have hk0 : 0 ≤ 16 * y ^ σ₀ * y ^ θ * (y - x) ^ (1 - θ) := by
      have : 0 ≤ (y - x) ^ (1 - θ) := Real.rpow_nonneg (by linarith) _
      positivity
    calc ‖(y : ℂ) * pk y (σ₀ + t * I) - (x : ℂ) * pk x (σ₀ + t * I)‖ *
          ‖G (σ₀ + t * I)‖
        ≤ (16 * y ^ σ₀ * y ^ θ * (y - x) ^ (1 - θ) * (1 + |t|) ^ (-(1 + θ))) *
            (C * (1 + |t|) ^ (θ / 2)) :=
          mul_le_mul hk hG' (norm_nonneg _) (by positivity)
      _ = K0 * ((1 + |t|) ^ (-(1 + θ)) * (1 + |t|) ^ (θ / 2)) := by rw [hK0]; ring
      _ = K0 * (1 + |t|) ^ (-(1 + θ / 2)) := by rw [← Real.rpow_add hw]; ring_nf
  have hnorm := norm_integral_le_of_norm_le hgint (Eventually.of_forall hpt)
  rw [integral_const_mul] at hnorm
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hlhs : ‖2 * Real.pi * (Ssum a y - Ssum a x)‖ = 2 * Real.pi * ‖Ssum a y - Ssum a x‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simp
  have hmain : 2 * Real.pi * ‖Ssum a y - Ssum a x‖ ≤ K0 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2)) := by
    rw [← hlhs, e]; exact hnorm
  have hI0 : 0 ≤ ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2)) :=
    integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  have hfin : ‖Ssum a y - Ssum a x‖ ≤ K0 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2)) := by
    have h0 := norm_nonneg (Ssum a y - Ssum a x)
    nlinarith
  refine hfin.trans (le_of_eq ?_)
  rw [hK0, Real.rpow_add hy0]
  ring

/-- Unsmoothing identity (adapted from `KerrPNT.Mobius.S_diff`): differences of `Ssum` recover
the partial sum up to `h²`. -/
lemma Ssum_diff {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (N h : ℕ) :
    ‖Ssum a (N + 1 / 2 + h) - Ssum a (N + 1 / 2) - h * ∑ n ∈ Finset.Iic N, a n‖ ≤ (h : ℝ) ^ 2 := by
  have hf1 : ⌊(N : ℝ) + 1 / 2⌋₊ = N := by
    rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
  have hf2 : ⌊(N : ℝ) + 1 / 2 + h⌋₊ = N + h := by
    rw [Nat.floor_eq_iff (by positivity)]; push_cast; constructor <;> linarith
  have hsplit : Finset.Iic (N + h) = Finset.Iic N ∪ Finset.Ioc N (N + h) := by
    ext n; simp only [Finset.mem_Iic, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Iic N) (Finset.Ioc N (N + h)) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Iic, Finset.mem_Ioc] at h1 h2; omega
  rw [Ssum, Ssum, hf1, hf2, hsplit, Finset.sum_union hdisj, Finset.mul_sum]
  have e : ∑ n ∈ Finset.Iic N, a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n) -
      ∑ n ∈ Finset.Iic N, a n * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) - n) -
      ∑ n ∈ Finset.Iic N, (h : ℂ) * a n = 0 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero; intro n _; push_cast; ring
  have : ∑ n ∈ Finset.Iic N, a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n) +
      ∑ n ∈ Finset.Ioc N (N + h), a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n) -
      ∑ n ∈ Finset.Iic N, a n * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) - n) -
      ∑ n ∈ Finset.Iic N, (h : ℂ) * a n =
      ∑ n ∈ Finset.Ioc N (N + h), a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n) := by
    linear_combination e
  rw [this]
  calc ‖∑ n ∈ Finset.Ioc N (N + h), a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n)‖
      ≤ ∑ n ∈ Finset.Ioc N (N + h), ‖a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc N (N + h), (h : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [Finset.mem_Ioc] at hn
        have h1 : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
        have h2 : (n : ℝ) ≤ N + h := by exact_mod_cast hn.2
        rw [norm_mul]
        have e2 : ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n) = (((N : ℝ) + 1 / 2 + h - n : ℝ) : ℂ) := by
          push_cast; ring
        rw [e2, Complex.norm_real, Real.norm_eq_abs]
        have hb : |(N : ℝ) + 1 / 2 + h - n| ≤ h := by
          rw [abs_le]; constructor <;> linarith
        calc ‖a n‖ * |(N : ℝ) + 1 / 2 + h - n| ≤ 1 * h :=
              mul_le_mul (ha n) hb (abs_nonneg _) zero_le_one
          _ = h := one_mul _
    _ = (h : ℝ) ^ 2 := by simp; ring

/-- **Partial sums from the smoothed bound.** Under the hypotheses of `Ssum_diff_bound`,
`‖∑_{n ≤ x} a(n)‖ ≤ (64 · 16 C I_θ + 2) x^{σ₀+θ}` for all `x ≥ 1` (with `h = ⌈√x⌉`). -/
theorem partial_sum_bound {a : ℕ → ℂ} (ha0 : a 0 = 0) (ha : ∀ n, ‖a n‖ ≤ 1) {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s) {σ₀ θ C : ℝ} (hσ₀ : 1 / 2 ≤ σ₀)
    (hσ₀2 : σ₀ ≤ 2) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C)
    (hGd : ∀ s : ℂ, σ₀ ≤ s.re → DifferentiableAt ℂ G s)
    (hGb : ∀ s : ℂ, σ₀ ≤ s.re → ‖G s‖ ≤ C * (1 + |s.im|) ^ (θ / 2)) {x : ℝ} (hx : 1 ≤ x) :
    ‖∑ n ∈ Finset.Iic ⌊x⌋₊, a n‖ ≤
      (64 * (16 * C * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2))) + 2) * x ^ (σ₀ + θ) := by
  set K' := 16 * C * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2)) with hK'
  have hI0 : 0 ≤ ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2)) :=
    MeasureTheory.integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  have hK'0 : 0 ≤ K' := by positivity
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊ with hN
  set h := ⌈Real.sqrt x⌉₊ with hh
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := Nat.le_floor (by simpa using hx)
    exact_mod_cast this
  have hsq1 : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; exact hx
  have hsqx : Real.sqrt x ≤ x := by
    have := Real.sqrt_le_sqrt (show x ≤ x ^ 2 by nlinarith)
    rwa [Real.sqrt_sq hx0.le] at this
  have hh1 : (1 : ℝ) ≤ h := by
    have : Real.sqrt x ≤ h := Nat.le_ceil _
    linarith
  have hhup : (h : ℝ) < Real.sqrt x + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  set z₁ : ℝ := N + 1 / 2 with hz₁
  set z₂ : ℝ := N + 1 / 2 + h with hz₂
  have hz₁1 : 1 ≤ z₁ := by linarith
  have hz12 : z₁ ≤ z₂ := by linarith
  have hd := Ssum_diff_bound ha0 ha hG hσ₀ hσ₀2 hθ0 hθ1 hC hGd hGb hz₁1 hz12
  rw [← hK'] at hd
  have hdiff := Ssum_diff ha N h
  have hz2x : z₂ ≤ 4 * x := by linarith
  have hexp0 : 0 ≤ σ₀ + θ := by linarith
  have hpow : z₂ ^ (σ₀ + θ) ≤ 64 * x ^ (σ₀ + θ) := by
    calc z₂ ^ (σ₀ + θ) ≤ (4 * x) ^ (σ₀ + θ) := Real.rpow_le_rpow (by linarith) hz2x hexp0
      _ = 4 ^ (σ₀ + θ) * x ^ (σ₀ + θ) := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 4 ^ (3 : ℝ) * x ^ (σ₀ + θ) := by
          gcongr
          · norm_num
          · linarith
      _ = 64 * x ^ (σ₀ + θ) := by norm_num
  have hhpow : (z₂ - z₁) ^ (1 - θ) ≤ h := by
    have e : z₂ - z₁ = h := by rw [hz₂, hz₁]; ring
    rw [e]
    calc (h : ℝ) ^ (1 - θ) ≤ (h : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hh1 (by linarith)
      _ = h := Real.rpow_one _
  have hd2 : ‖Ssum a z₂ - Ssum a z₁‖ ≤ K' * (64 * x ^ (σ₀ + θ)) * h := by
    refine hd.trans ?_
    have : 0 ≤ (z₂ - z₁) ^ (1 - θ) := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ z₂ ^ (σ₀ + θ) := Real.rpow_nonneg (by linarith) _
    gcongr
  -- `h ‖A‖ ≤ ‖ΔS‖ + h²`
  set A : ℂ := ∑ n ∈ Finset.Iic N, a n with hAdef
  set D : ℂ := Ssum a z₂ - Ssum a z₁ with hDdef
  have hdiff' : ‖D - (h : ℂ) * A‖ ≤ (h : ℝ) ^ 2 := by
    simpa [hz₁, hz₂, hDdef, hAdef] using hdiff
  have hA : (h : ℝ) * ‖A‖ ≤ K' * (64 * x ^ (σ₀ + θ)) * h + (h : ℝ) ^ 2 := by
    have e1 : (h : ℝ) * ‖A‖ = ‖(h : ℂ) * A‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [e1]
    have t1 := norm_sub_le D (D - (h : ℂ) * A)
    have e2 : D - (D - (h : ℂ) * A) = (h : ℂ) * A := by ring
    rw [e2] at t1
    linarith
  have hA2 : ‖A‖ ≤ K' * (64 * x ^ (σ₀ + θ)) + h := by
    have hhpos : (0 : ℝ) < h := by linarith
    have : (h : ℝ) * ‖A‖ ≤ (h : ℝ) * (K' * (64 * x ^ (σ₀ + θ)) + h) := by
      nlinarith
    exact le_of_mul_le_mul_left this hhpos
  have hsqpow : Real.sqrt x ≤ x ^ (σ₀ + θ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hxpow : 1 ≤ x ^ (σ₀ + θ) := Real.one_le_rpow hx hexp0
  have h3 : (h : ℝ) ≤ 2 * x ^ (σ₀ + θ) := by linarith
  have e : K' * (64 * x ^ (σ₀ + θ)) + 2 * x ^ (σ₀ + θ) = (64 * K' + 2) * x ^ (σ₀ + θ) := by ring
  linarith

end FleetLandauTransfer
