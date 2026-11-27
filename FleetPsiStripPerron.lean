import FleetLandauTransferPerron

/-!
# Perron's formula and partial sums for polynomially bounded coefficients

`FleetLandauTransferPerron` proves the smoothed Perron identity, the contour shift and the
partial-sum bound for coefficients with `‖a n‖ ≤ 1` (the Möbius case). For `ψ` the coefficients
are `Λ(n) − 1`, which are only `≪ n^κ` for every `κ > 0`. This file repeats the four steps with the
hypothesis `‖a n‖ ≤ B n^κ`; the proofs are those of `FleetLandauTransferPerron` (themselves adapted
from kerr-lean `Kerr/Zeta/Littlewood.lean`, James C. Kerr, Apache-2.0), changed only where the
coefficient bound enters: the summability in `perron_general'` (`∑ B n^{κ−b}` with `κ < b − 1`) and
the unsmoothing error in `Ssum_diff'` (`h² B (N+h)^κ` instead of `h²`). `vertical_shift`,
`kernel_bound` are reused unchanged.

* `perron_general'`: `∫ pk x (b+it) G(b+it) dt = 2π ∑_{n ≤ x} a(n)(1 − n/x)` for `x > 0`, `b > 1 + κ`.
* `Ssum_diff_bound'`: the smoothed-sum difference bound, `κ < 1`.
* `partial_sum_bound'`: `‖∑_{n ≤ x} a(n)‖ ≤ (64 · 16 C I_θ + 6B) x^{σ₀+θ}` for `x ≥ 1`, when
  `0 ≤ κ < 1` and `1/2 + κ ≤ σ₀ + θ`.
-/

noncomputable section
open Complex Set Filter Topology MeasureTheory
open scoped Interval

namespace FleetPsiStrip

open FleetLandauTransfer

/-- **Smoothed Perron identity** for coefficients with `‖a n‖ ≤ B n^κ`, `κ < b − 1`
(`FleetLandauTransfer.perron_general` with the coefficient bound generalized). -/
theorem perron_general' {a : ℕ → ℂ} (ha0 : a 0 = 0) {B κ : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ B * (n : ℝ) ^ κ) {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s) {x b : ℝ} (hx : 0 < x) (hb : 1 < b)
    (hκ : κ < b - 1) :
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
  have hbound : ∀ n, ∫ t, ‖g n t‖ ≤ x ^ b * B * K * (n : ℝ) ^ (κ - b) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [hg, Real.zero_rpow (by linarith : κ - b ≠ 0)]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have e : ∀ t : ℝ, ‖g n t‖ ≤ x ^ b * B * (n : ℝ) ^ (κ - b) * ‖pk 1 (b + t * I)‖ := by
        intro t
        simp only [hg, hn, ite_false, norm_mul]
        rw [norm_pk (div_pos hx hnpos)]
        have hre : ((b : ℂ) + t * I).re = b := by simp
        rw [hre, Real.div_rpow hx.le hnpos.le, div_eq_mul_inv, ← Real.rpow_neg hnpos.le]
        have hp : 0 ≤ x ^ b * (n : ℝ) ^ (-b) * ‖pk 1 (b + t * I)‖ := by positivity
        calc ‖a n‖ * (x ^ b * (n : ℝ) ^ (-b) * ‖pk 1 (b + t * I)‖)
            ≤ (B * (n : ℝ) ^ κ) * (x ^ b * (n : ℝ) ^ (-b) * ‖pk 1 (b + t * I)‖) :=
              mul_le_mul_of_nonneg_right (ha n) hp
          _ = x ^ b * B * ((n : ℝ) ^ κ * (n : ℝ) ^ (-b)) * ‖pk 1 (b + t * I)‖ := by ring
          _ = _ := by rw [← Real.rpow_add hnpos, ← sub_eq_add_neg]
      calc ∫ t, ‖g n t‖ ≤ ∫ t : ℝ, x ^ b * B * (n : ℝ) ^ (κ - b) * ‖pk 1 (b + t * I)‖ :=
            integral_mono (hint n).norm (hK1.const_mul _) e
        _ = x ^ b * B * K * (n : ℝ) ^ (κ - b) := by rw [integral_const_mul]; ring
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

lemma two_pi_Ssum' {a : ℕ → ℂ} (ha0 : a 0 = 0) {B κ : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ B * (n : ℝ) ^ κ) (hκ : κ < 1) {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s) {x : ℝ} (hx : 0 < x) :
    2 * Real.pi * Ssum a x = x * ∫ t : ℝ, pk x ((2 : ℝ) + t * I) * G ((2 : ℝ) + t * I) := by
  rw [perron_general' ha0 ha hG hx (by norm_num : (1 : ℝ) < 2) (by linarith), Ssum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp

/-- **Difference bound for the smoothed sums**, coefficients `‖a n‖ ≤ B n^κ`, `κ < 1`
(`FleetLandauTransfer.Ssum_diff_bound` with the coefficient bound generalized). -/
theorem Ssum_diff_bound' {a : ℕ → ℂ} (ha0 : a 0 = 0) {B κ : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ B * (n : ℝ) ^ κ) (hκ : κ < 1) {G : ℂ → ℂ}
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
  have hsx := two_pi_Ssum' ha0 ha hκ hG hx0
  have hsy := two_pi_Ssum' ha0 ha hκ hG hy0
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

/-- Unsmoothing identity for `‖a n‖ ≤ B n^κ`, `κ ≥ 0` (`FleetLandauTransfer.Ssum_diff` with the
error `h²` replaced by `h² B (N+h)^κ`). -/
lemma Ssum_diff' {a : ℕ → ℂ} {B κ : ℝ} (ha : ∀ n, ‖a n‖ ≤ B * (n : ℝ) ^ κ) (hκ : 0 ≤ κ)
    (N h : ℕ) :
    ‖Ssum a (N + 1 / 2 + h) - Ssum a (N + 1 / 2) - h * ∑ n ∈ Finset.Iic N, a n‖ ≤
      (h : ℝ) ^ 2 * (B * ((N : ℝ) + h) ^ κ) := by
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
  set Q : ℝ := B * ((N : ℝ) + h) ^ κ with hQ
  calc ‖∑ n ∈ Finset.Ioc N (N + h), a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n)‖
      ≤ ∑ n ∈ Finset.Ioc N (N + h), ‖a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc N (N + h), Q * (h : ℝ) := by
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
        have han : ‖a n‖ ≤ Q := by
          refine (ha n).trans ?_
          have hB : 0 ≤ B := by
            have := (norm_nonneg (a n)).trans (ha n)
            have hn0 : (0 : ℝ) < n := by linarith
            exact nonneg_of_mul_nonneg_left this (Real.rpow_pos_of_pos hn0 _)
          rw [hQ]
          gcongr
        have hQ0 : 0 ≤ Q := (norm_nonneg _).trans han
        exact mul_le_mul han hb (abs_nonneg _) hQ0
    _ = (h : ℝ) ^ 2 * Q := by simp; ring

/-- **Partial sums from the smoothed bound**, coefficients `‖a n‖ ≤ B n^κ` with `0 ≤ κ < 1` and
`1/2 + κ ≤ σ₀ + θ`: `‖∑_{n ≤ x} a(n)‖ ≤ (64 · 16 C I_θ + 6B) x^{σ₀+θ}` for `x ≥ 1`
(`FleetLandauTransfer.partial_sum_bound` with the coefficient bound generalized; `h = ⌈√x⌉`). -/
theorem partial_sum_bound' {a : ℕ → ℂ} (ha0 : a 0 = 0) {B κ : ℝ} (hB : 0 ≤ B)
    (ha : ∀ n, ‖a n‖ ≤ B * (n : ℝ) ^ κ) (hκ0 : 0 ≤ κ) (hκ : κ < 1) {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s) {σ₀ θ C : ℝ} (hσ₀ : 1 / 2 ≤ σ₀)
    (hσ₀2 : σ₀ ≤ 2) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hκσ : 1 / 2 + κ ≤ σ₀ + θ) (hC : 0 ≤ C)
    (hGd : ∀ s : ℂ, σ₀ ≤ s.re → DifferentiableAt ℂ G s)
    (hGb : ∀ s : ℂ, σ₀ ≤ s.re → ‖G s‖ ≤ C * (1 + |s.im|) ^ (θ / 2)) {x : ℝ} (hx : 1 ≤ x) :
    ‖∑ n ∈ Finset.Iic ⌊x⌋₊, a n‖ ≤
      (64 * (16 * C * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2))) + 6 * B) * x ^ (σ₀ + θ) := by
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
  have hd := Ssum_diff_bound' ha0 ha hκ hG hσ₀ hσ₀2 hθ0 hθ1 hC hGd hGb hz₁1 hz12
  rw [← hK'] at hd
  have hdiff := Ssum_diff' ha hκ0 N h
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
  -- `h ‖A‖ ≤ ‖ΔS‖ + h² Q`
  set Q : ℝ := B * ((N : ℝ) + h) ^ κ with hQ
  set A : ℂ := ∑ n ∈ Finset.Iic N, a n with hAdef
  set D : ℂ := Ssum a z₂ - Ssum a z₁ with hDdef
  have hdiff' : ‖D - (h : ℂ) * A‖ ≤ (h : ℝ) ^ 2 * Q := by
    simpa [hz₁, hz₂, hDdef, hAdef, hQ] using hdiff
  have hA : (h : ℝ) * ‖A‖ ≤ K' * (64 * x ^ (σ₀ + θ)) * h + (h : ℝ) ^ 2 * Q := by
    have e1 : (h : ℝ) * ‖A‖ = ‖(h : ℂ) * A‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [e1]
    have t1 := norm_sub_le D (D - (h : ℂ) * A)
    have e2 : D - (D - (h : ℂ) * A) = (h : ℂ) * A := by ring
    rw [e2] at t1
    linarith
  have hA2 : ‖A‖ ≤ K' * (64 * x ^ (σ₀ + θ)) + h * Q := by
    have hhpos : (0 : ℝ) < h := by linarith
    have : (h : ℝ) * ‖A‖ ≤ (h : ℝ) * (K' * (64 * x ^ (σ₀ + θ)) + h * Q) := by
      nlinarith
    exact le_of_mul_le_mul_left this hhpos
  -- `h Q ≤ 6 B x^{σ₀+θ}`
  have hh2 : (h : ℝ) ≤ 2 * Real.sqrt x := by linarith
  have hNh : (N : ℝ) + h ≤ 3 * x := by linarith
  have hNh0 : (0 : ℝ) ≤ (N : ℝ) + h := by positivity
  have hQle : Q ≤ B * (3 * x ^ κ) := by
    rw [hQ]
    gcongr
    calc ((N : ℝ) + h) ^ κ ≤ (3 * x) ^ κ := Real.rpow_le_rpow hNh0 hNh hκ0
      _ = 3 ^ κ * x ^ κ := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 3 ^ (1 : ℝ) * x ^ κ := by
          gcongr
          norm_num
      _ = 3 * x ^ κ := by norm_num
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hsqκ : Real.sqrt x * x ^ κ ≤ x ^ (σ₀ + θ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hhQ : (h : ℝ) * Q ≤ 6 * B * x ^ (σ₀ + θ) := by
    calc (h : ℝ) * Q ≤ (2 * Real.sqrt x) * (B * (3 * x ^ κ)) :=
          mul_le_mul hh2 hQle hQ0 (by positivity)
      _ = 6 * B * (Real.sqrt x * x ^ κ) := by ring
      _ ≤ 6 * B * x ^ (σ₀ + θ) := by gcongr
  have e : K' * (64 * x ^ (σ₀ + θ)) + 6 * B * x ^ (σ₀ + θ) =
      (64 * K' + 6 * B) * x ^ (σ₀ + θ) := by ring
  linarith

end FleetPsiStrip
