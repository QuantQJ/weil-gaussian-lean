import FleetExplicitPNTBounds
import PsiContourProbe
import QuasiRHWiring

/-!
# An explicit-constant prime number theorem from the quasi-Riemann hypothesis

**Main theorem** (`psi_explicit_of_quasiRH`): if `ζ(s) ≠ 0` for `Re s > 7/8`
(`QuasiRHWiring.QuasiRH`, carried as a hypothesis), then

  `|ψ(x) − x| ≤ 12000 · x^{7/8} · (log x)²`   for every real `x ≥ 1000`,

with `ψ = Chebyshev.psi` (Mathlib). Both constants are numerals in the statement.

**Route.** The exact contour identity of hp-proof at the zero-avoiding heights
(`PsiContourProbe.contour_identity_of_continuous`, rectangle `[−1/2, 3/2] × [−T, T]`), applied to
the continuous kernel `g(u) = e^{u/2}` on `[−log x, log x]`, whose transform is the entire Perron
kernel `G(s) = (x^s − x^{−s})/s` (`Gt_g0`). Then:

* right edge `Re s = 3/2`: `−(1/2π)∫ ζ'/ζ · G = ∑ Λ(n) K(x/n) − ∑ Λ(n) K(1/(xn))`
  (`right_edge_eq`), compared with `ψ(x)` at half-integers `x = N + 1/2` by the truncated Perron
  bounds of `FleetExplicitPNTKernel` (error `≤ 80 x^{5/2}/(πT) + 20/(πT log x)`);
* zeros: `|G(ρ)| ≤ (x^{7/8} + 1)/|ρ|` under quasi-RH, and `∑_{|Im ρ| ≤ T} m(ρ)/|ρ| ≤ 47 + 600 log² T`
  (`FleetExplicitPNTBounds.sum_zetaOrder_div_norm_le`);
* horizontal edges: `‖ζ'/ζ‖ ≤ B log² T ≤ 26000 log² T` (`HorizontalVanishingSeq`), `|G| ≤ 2x^{3/2}/T`;
* left edge `Re s = −1/2`: `‖ζ'/ζ‖ ≤ 30 + 2 log(5/2 + |t|)`, `|G| ≤ 6 x^{1/2}/(1 + |t|)`;
* `T = heights (N² + N) ∈ [x², x² + 5]`.

At half-integers this gives `|ψ(x) − x| ≤ 11600 x^{7/8} log² x` (`psi_halfint_explicit_of_quasiRH`,
`N ≥ 999`); the general `x` follows since `ψ(x) = ψ(⌊x⌋ + 1/2)`.
-/

noncomputable section
open Complex Filter Topology Set Reduction PrincipalPartDischarge
open scoped Real Interval ArithmeticFunction.vonMangoldt

namespace FleetExplicitPNT

open FleetExplicitPNTKernel FleetExplicitPNTBounds

/-! ## The kernel `g(u) = e^{u/2}` and its transform -/

/-- `g₀(u) = e^{u/2}`. -/
def g0 : ℝ → ℂ := fun u => Complex.exp ((u : ℂ) / 2)

theorem continuous_g0 : Continuous g0 := by unfold g0; fun_prop

/-- **`Gt (log x) g₀ s = (x^s − x^{−s})/s`** for `x > 0`, `s ≠ 0`. -/
theorem Gt_g0 {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) :
    TestFunctions.Gt (Real.log x) g0 s = ((x : ℂ) ^ s - (x : ℂ) ^ (-s)) / s := by
  unfold TestFunctions.Gt g0
  have e : ∀ u : ℝ, Complex.exp ((u : ℂ) / 2) * Complex.exp ((s - 1 / 2) * u) =
      Complex.exp (s * u) := by
    intro u; rw [← Complex.exp_add]; congr 1; ring
  simp_rw [e]
  rw [integral_exp_mul_complex hs]
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero hx', Complex.cpow_def_of_ne_zero hx',
    ← Complex.ofReal_log hx.le]
  push_cast
  ring_nf

/-- `‖(x^s − x^{−s})/s‖ ≤ (x^{Re s} + x^{−Re s})/‖s‖`. -/
theorem norm_G_le {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖((x : ℂ) ^ s - (x : ℂ) ^ (-s)) / s‖ ≤ (x ^ s.re + x ^ (-s.re)) / ‖s‖ := by
  rw [norm_div]
  gcongr
  refine (norm_sub_le _ _).trans ?_
  rw [norm_cpow_eq_rpow_re_of_pos hx, norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]

/-- `G(1) = x − 1/x`. -/
theorem Gt_g0_one {x : ℝ} (hx : 0 < x) :
    TestFunctions.Gt (Real.log x) g0 1 = (x : ℂ) - (x : ℂ)⁻¹ := by
  rw [Gt_g0 hx one_ne_zero, Complex.cpow_one, Complex.cpow_neg_one, div_one]

/-! ## The right edge as two Perron sums -/

lemma cpow_neg_eq_inv_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ (-s) = (((1 / x : ℝ)) : ℂ) ^ s := by
  rw [Complex.cpow_neg, one_div, Complex.ofReal_inv, inv_cpow_ofReal_nonneg hx.le]

/-- **Right edge.** For `x > 0`, `T ≥ 0`:
`∫_{-T}^{T} ζ'/ζ(3/2+iy) G(3/2+iy) dy = −2π (∑ Λ(n) K(x/n) − ∑ Λ(n) K((1/x)/n))`. -/
theorem right_edge_eq {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) :
    (∫ y in (-T)..T, deriv riemannZeta (3 / 2 + y * I) / riemannZeta (3 / 2 + y * I) *
        TestFunctions.Gt (Real.log x) g0 (3 / 2 + y * I)) =
      -(2 * π) * ((∑' n : ℕ, (Λ n : ℂ) * kernel (x / n) (3 / 2) T) -
        ∑' n : ℕ, (Λ n : ℂ) * kernel ((1 / x) / n) (3 / 2) T) := by
  have h1 := perron_integral_eq_tsum (x := x) (c := 3 / 2) (T := T) hx (by norm_num) hT
  have h2 := perron_integral_eq_tsum (x := 1 / x) (c := 3 / 2) (T := T) (by positivity)
    (by norm_num) hT
  have e32 : ((3 / 2 : ℝ) : ℂ) = 3 / 2 := by push_cast; ring
  rw [e32] at h1 h2
  have hs0 : ∀ y : ℝ, (3 / 2 + y * I : ℂ) ≠ 0 := by
    intro y h; have := congrArg Complex.re h; norm_num at this
  have hcL := LeftLineBound.continuous_logDeriv_right_line
  have hline : Continuous fun y : ℝ => (3 / 2 + y * I : ℂ) := by fun_prop
  have hneg : Continuous fun y : ℝ =>
      (-(deriv riemannZeta (3 / 2 + y * I))) / riemannZeta (3 / 2 + y * I) :=
    hcL.neg.congr fun y => by simp only [Pi.neg_apply, neg_div]
  have hcA : ∀ z : ℝ, 0 < z → Continuous fun y : ℝ =>
      (-(deriv riemannZeta (3 / 2 + y * I))) / riemannZeta (3 / 2 + y * I) *
        ((z : ℂ) ^ (3 / 2 + y * I) / (3 / 2 + y * I)) := by
    intro z hz
    have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    exact hneg.mul ((hline.const_cpow (Or.inl hz')).div hline hs0)
  have hpt : ∀ y : ℝ, deriv riemannZeta (3 / 2 + y * I) / riemannZeta (3 / 2 + y * I) *
      TestFunctions.Gt (Real.log x) g0 (3 / 2 + y * I) =
      -((-(deriv riemannZeta (3 / 2 + y * I))) / riemannZeta (3 / 2 + y * I) *
        ((x : ℂ) ^ (3 / 2 + y * I) / (3 / 2 + y * I))) +
      (-(deriv riemannZeta (3 / 2 + y * I))) / riemannZeta (3 / 2 + y * I) *
        ((((1 / x : ℝ)) : ℂ) ^ (3 / 2 + y * I) / (3 / 2 + y * I)) := by
    intro y
    rw [Gt_g0 hx (hs0 y), cpow_neg_eq_inv_cpow hx]
    ring
  simp_rw [hpt]
  have hi1 : IntervalIntegrable (fun y : ℝ =>
      -((-(deriv riemannZeta (3 / 2 + y * I))) / riemannZeta (3 / 2 + y * I) *
        ((x : ℂ) ^ (3 / 2 + y * I) / (3 / 2 + y * I)))) MeasureTheory.volume (-T) T :=
    ((hcA x hx).neg).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun y : ℝ =>
      (-(deriv riemannZeta (3 / 2 + y * I))) / riemannZeta (3 / 2 + y * I) *
        ((((1 / x : ℝ)) : ℂ) ^ (3 / 2 + y * I) / (3 / 2 + y * I))) MeasureTheory.volume (-T) T :=
    (hcA (1 / x) (by positivity)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_neg, h1, h2]
  ring

/-! ## The horizontal and left edges -/

/-- `‖G(σ + iT')‖ ≤ 2 x^{3/2}/|T'|` on `σ ∈ [−1/2, 3/2]`, `x ≥ 1`. -/
theorem norm_G_horiz_le {x : ℝ} (hx : 1 ≤ x) {σ T' : ℝ} (hσ : σ ∈ Icc (-1 / 2 : ℝ) (3 / 2))
    (hT' : T' ≠ 0) :
    ‖TestFunctions.Gt (Real.log x) g0 (σ + T' * I)‖ ≤ 2 * x ^ (3 / 2 : ℝ) / |T'| := by
  have hx0 : 0 < x := by linarith
  have hs0 : (σ + T' * I : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hT' this
  rw [Gt_g0 hx0 hs0]
  refine (norm_G_le hx0 _).trans ?_
  have hre : (σ + T' * I : ℂ).re = σ := by simp
  rw [hre]
  have hnorm : |T'| ≤ ‖(σ + T' * I : ℂ)‖ := by
    have := Complex.abs_im_le_norm (σ + T' * I : ℂ); simpa using this
  have h1 : x ^ σ ≤ x ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ.2
  have h2 : x ^ (-σ) ≤ x ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith [hσ.1])
  have hT0 : 0 < |T'| := abs_pos.mpr hT'
  calc (x ^ σ + x ^ (-σ)) / ‖(σ + T' * I : ℂ)‖ ≤ (x ^ σ + x ^ (-σ)) / |T'| := by
        gcongr
    _ ≤ 2 * x ^ (3 / 2 : ℝ) / |T'| := by gcongr; linarith

/-- `‖G(−1/2 + it)‖ ≤ 6 x^{1/2}/(1 + |t|)`, `x ≥ 1`. -/
theorem norm_G_left_le {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    ‖TestFunctions.Gt (Real.log x) g0 (-1 / 2 + t * I)‖ ≤ 6 * x ^ (1 / 2 : ℝ) * (1 + |t|)⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hs0 : (-1 / 2 + t * I : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [Gt_g0 hx0 hs0]
  refine (norm_G_le hx0 _).trans ?_
  have hre : (-1 / 2 + t * I : ℂ).re = -1 / 2 := by simp
  rw [hre]
  have hnorm : (1 + |t|) / 3 ≤ ‖(-1 / 2 + t * I : ℂ)‖ := by
    have hsq : ‖(-1 / 2 + t * I : ℂ)‖ ^ 2 = 1 / 4 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
    have h0 : 0 ≤ ‖(-1 / 2 + t * I : ℂ)‖ := norm_nonneg _
    have : ((1 + |t|) / 3) ^ 2 ≤ ‖(-1 / 2 + t * I : ℂ)‖ ^ 2 := by
      rw [hsq]; nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t| - 1 / 8)]
    exact (pow_le_pow_iff_left₀ (by positivity) h0 two_ne_zero).mp this
  have h1 : x ^ (-1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have h2 : x ^ (-(-1 / 2) : ℝ) = x ^ (1 / 2 : ℝ) := by norm_num
  rw [h2]
  have hpos : 0 < (1 + |t|) / 3 := by positivity
  have hx12 : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  calc (x ^ (-1 / 2 : ℝ) + x ^ (1 / 2 : ℝ)) / ‖(-1 / 2 + t * I : ℂ)‖
      ≤ (2 * x ^ (1 / 2 : ℝ)) / ((1 + |t|) / 3) :=
        div_le_div₀ (by positivity) (by linarith) hpos hnorm
    _ = 6 * x ^ (1 / 2 : ℝ) * (1 + |t|)⁻¹ := by field_simp; ring

/-- **Horizontal edge.** If `‖ζ'/ζ(σ + iT')‖ ≤ M` on `[−1/2, 3/2]` (`T' ≠ 0`, `M ≥ 0`, `x ≥ 1`), then
`‖∫_{−1/2}^{3/2} ζ'/ζ(σ+iT') G(σ+iT') dσ‖ ≤ 4 M x^{3/2}/|T'|`. -/
theorem horiz_edge_le {x : ℝ} (hx : 1 ≤ x) {T' M : ℝ} (hT' : T' ≠ 0) (hM : 0 ≤ M)
    (hb : ∀ σ ∈ Icc (-1 / 2 : ℝ) (3 / 2),
      ‖deriv riemannZeta (σ + T' * I) / riemannZeta (σ + T' * I)‖ ≤ M) :
    ‖∫ σ in (-1 / 2 : ℝ)..(3 / 2), deriv riemannZeta (σ + T' * I) / riemannZeta (σ + T' * I) *
        TestFunctions.Gt (Real.log x) g0 (σ + T' * I)‖ ≤ 4 * M * x ^ (3 / 2 : ℝ) / |T'| := by
  have hT0 : 0 < |T'| := abs_pos.mpr hT'
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -1 / 2) (b := 3 / 2)
    (C := M * (2 * x ^ (3 / 2 : ℝ) / |T'|))
    (f := fun σ : ℝ => deriv riemannZeta (σ + T' * I) / riemannZeta (σ + T' * I) *
        TestFunctions.Gt (Real.log x) g0 (σ + T' * I)) (fun σ hσ => by
      rw [Set.uIoc_of_le (by norm_num)] at hσ
      have hσ' : σ ∈ Icc (-1 / 2 : ℝ) (3 / 2) := ⟨hσ.1.le, hσ.2⟩
      rw [norm_mul]
      exact mul_le_mul (hb σ hσ') (norm_G_horiz_le hx hσ' hT') (norm_nonneg _) hM)
  refine h.trans (le_of_eq ?_)
  rw [show |(3 / 2 : ℝ) - -1 / 2| = 2 by norm_num]
  ring

/-- **Left edge.** For `x ≥ 1`, `T ≥ 0`:
`‖∫_{-T}^{T} ζ'/ζ(−1/2+it) G(−1/2+it) dt‖ ≤ (30 + 2 log(5/2 + T)) · 6 x^{1/2} · 2 log(1 + T)`. -/
theorem left_edge_le {x : ℝ} (hx : 1 ≤ x) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ y in (-T)..T, deriv riemannZeta (-1 / 2 + y * I) / riemannZeta (-1 / 2 + y * I) *
        TestFunctions.Gt (Real.log x) g0 (-1 / 2 + y * I)‖ ≤
      (30 + 2 * Real.log (5 / 2 + T)) * (6 * x ^ (1 / 2 : ℝ)) * (2 * Real.log (1 + T)) := by
  have hx0 : 0 < x := by linarith
  set K : ℝ := (30 + 2 * Real.log (5 / 2 + T)) * (6 * x ^ (1 / 2 : ℝ)) with hK
  have hc : Continuous fun t : ℝ => (1 + |t|)⁻¹ :=
    (continuous_const.add continuous_abs).inv₀
      (fun t => (add_pos_of_pos_of_nonneg one_pos (abs_nonneg t)).ne')
  have h := intervalIntegral.norm_integral_le_of_norm_le (a := -T) (b := T) (by linarith)
    (f := fun y : ℝ => deriv riemannZeta (-1 / 2 + y * I) / riemannZeta (-1 / 2 + y * I) *
        TestFunctions.Gt (Real.log x) g0 (-1 / 2 + y * I))
    (g := fun t : ℝ => K * (1 + |t|)⁻¹)
    (Eventually.of_forall fun t ht => by
      have hta : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
      rw [norm_mul]
      have h1 := FleetExplicitPNTBounds.norm_logDeriv_zeta_left_le t
      have h1' : 30 + 2 * Real.log (5 / 2 + |t|) ≤ 30 + 2 * Real.log (5 / 2 + T) := by
        have := Real.log_le_log (by positivity) (by linarith : 5 / 2 + |t| ≤ 5 / 2 + T)
        linarith
      have h2 := norm_G_left_le hx t
      have hl0 : 0 ≤ 30 + 2 * Real.log (5 / 2 + T) := by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 5 / 2 + T); linarith
      calc ‖deriv riemannZeta (-1 / 2 + t * I) / riemannZeta (-1 / 2 + t * I)‖ *
            ‖TestFunctions.Gt (Real.log x) g0 (-1 / 2 + t * I)‖
          ≤ (30 + 2 * Real.log (5 / 2 + T)) * (6 * x ^ (1 / 2 : ℝ) * (1 + |t|)⁻¹) :=
            mul_le_mul (h1.trans h1') h2 (norm_nonneg _) hl0
        _ = K * (1 + |t|)⁻¹ := by rw [hK]; ring)
    ((hc.intervalIntegrable (μ := MeasureTheory.volume) _ _).const_mul K)
  refine h.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_inv_one_add_abs hT]

/-- **Zero side under quasi-RH.** For `x ≥ 1`, `T ≥ 4`:
`‖∑_{ρ} m(ρ) G(ρ)‖ ≤ (x^{7/8} + 1)(47 + 600 log² T)`. -/
theorem zero_side_le (hQ : QuasiRHWiring.QuasiRH) {x : ℝ} (hx : 1 ≤ x) {T : ℝ} (hT : 4 ≤ T) :
    ‖∑ ρ ∈ zeroFinset (3 / 2) T, (zetaOrder ρ : ℂ) * TestFunctions.Gt (Real.log x) g0 ρ‖ ≤
      (x ^ (7 / 8 : ℝ) + 1) * (47 + 600 * Real.log T ^ 2) := by
  classical
  have hx0 : 0 < x := by linarith
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ ρ ∈ zeroFinset (3 / 2) T,
      ‖(zetaOrder ρ : ℂ) * TestFunctions.Gt (Real.log x) g0 ρ‖ ≤
        (x ^ (7 / 8 : ℝ) + 1) * ((zetaOrder ρ : ℝ) / ‖ρ‖) := by
    intro ρ hρ
    have hnt := ((ZeroSumLimit.mem_zeroFinset_three_halves (by linarith)).mp hρ).1
    obtain ⟨h0, -⟩ := ZetaStrip.mem_strip_of_isNontrivialZero hnt
    have h78 := QuasiRHWiring.re_le_of_quasiRH hQ hnt
    have hρ0 : ρ ≠ 0 := by intro h; rw [h] at h0; simp at h0
    have hnρ : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
    rw [norm_mul, Gt_g0 hx0 hρ0, Complex.norm_natCast]
    have hG := norm_G_le hx0 ρ
    have h1 : x ^ ρ.re ≤ x ^ (7 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx h78
    have h2 : x ^ (-ρ.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
    have hG' : ‖((x : ℂ) ^ ρ - (x : ℂ) ^ (-ρ)) / ρ‖ ≤ (x ^ (7 / 8 : ℝ) + 1) / ‖ρ‖ :=
      hG.trans (by gcongr)
    calc (zetaOrder ρ : ℝ) * ‖((x : ℂ) ^ ρ - (x : ℂ) ^ (-ρ)) / ρ‖
        ≤ (zetaOrder ρ : ℝ) * ((x ^ (7 / 8 : ℝ) + 1) / ‖ρ‖) := by gcongr
      _ = (x ^ (7 / 8 : ℝ) + 1) * ((zetaOrder ρ : ℝ) / ‖ρ‖) := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hx78 : 0 ≤ x ^ (7 / 8 : ℝ) + 1 := by positivity
  exact mul_le_mul_of_nonneg_left (FleetExplicitPNTBounds.sum_zetaOrder_div_norm_le hT) hx78

/-! ## Assembly -/

/-- The algebra of the contour identity: from `bot − top + I R − I Lf = 2πI (Z − G₁)`,
`R = −2π (P₁ − P₂)` and `G₁ = x − x⁻¹`,
`‖ψ − x‖ ≤ ‖ψ − P₁‖ + ‖x⁻¹‖ + ‖Z‖ + ‖P₂‖ + (‖bot‖ + ‖top‖ + ‖Lf‖)/(2π)`. -/
theorem contour_algebra {ψ x P₁ P₂ Z G₁ R bot top Lf : ℂ}
    (hId : bot - top + I * R - I * Lf = 2 * (π : ℂ) * I * (Z - G₁))
    (hR : R = -(2 * π) * (P₁ - P₂)) (hG : G₁ = x - x⁻¹) :
    ‖ψ - x‖ ≤ ‖ψ - P₁‖ + ‖x⁻¹‖ + ‖Z‖ + ‖P₂‖ + (‖bot‖ + ‖top‖ + ‖Lf‖) / (2 * π) := by
  have key : 2 * (π : ℂ) * I * (ψ - x) =
      2 * (π : ℂ) * I * ((ψ - P₁) - x⁻¹ - Z + P₂) + (bot - top - I * Lf) := by
    linear_combination -hId + I * hR + 2 * (π : ℂ) * I * hG
  have hn : ‖2 * (π : ℂ) * I‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, norm_I, mul_one]
  have hpi : 0 < 2 * π := by positivity
  have h1 : 2 * π * ‖ψ - x‖ ≤ 2 * π * (‖ψ - P₁‖ + ‖x⁻¹‖ + ‖Z‖ + ‖P₂‖) +
      (‖bot‖ + ‖top‖ + ‖Lf‖) := by
    have := congrArg norm key
    rw [norm_mul, hn] at this
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, hn]
      gcongr
      refine (norm_add_le _ _).trans ?_
      gcongr
      refine (norm_sub_le _ _).trans ?_
      gcongr
      exact norm_sub_le _ _
    · refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_I, one_mul]
      gcongr
      exact norm_sub_le _ _
  have e : ‖ψ - P₁‖ + ‖x⁻¹‖ + ‖Z‖ + ‖P₂‖ + (‖bot‖ + ‖top‖ + ‖Lf‖) / (2 * π) =
      (2 * π * (‖ψ - P₁‖ + ‖x⁻¹‖ + ‖Z‖ + ‖P₂‖) + (‖bot‖ + ‖top‖ + ‖Lf‖)) / (2 * π) := by
    field_simp
  rw [e, le_div_iff₀ hpi]
  linarith

/-! ### Numerical lemmas (abstract reals, small contexts) -/

lemma num_perron {x T Q : ℝ} (hT0 : 0 < T) (hTx2 : x ^ 2 ≤ T) (hQ0 : 0 ≤ Q) :
    80 * (x ^ 2 * Q) / (π * T) ≤ 27 * Q := by
  have hpi3 := Real.pi_gt_three
  rw [div_le_iff₀ (by positivity)]
  have h1 : 80 * x ^ 2 ≤ 27 * (π * T) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hQ0]

lemma num_small {x T : ℝ} (hT4 : 4 ≤ T) (hL1 : 1 ≤ Real.log x) :
    20 / (π * T * Real.log x) ≤ 2 := by
  have hpi3 := Real.pi_gt_three
  rw [div_le_iff₀ (by positivity)]
  have h1 : 12 ≤ π * T := by nlinarith
  nlinarith

lemma num_edge {B LT L x Q P T : ℝ} (hB : B ≤ 26000) (hLT0 : 0 ≤ LT)
    (hLT : LT ≤ 3 * L) (hx0 : 0 < x) (hQ0 : 0 ≤ Q) (hQP : Q ≤ P) (hxT : 999 * x ≤ T)
    (hT0 : 0 < T) :
    4 * (B * LT ^ 2) * (x * Q) / T ≤ 937 * L ^ 2 * P := by
  have hLT2 : LT ^ 2 ≤ 9 * L ^ 2 := by
    calc LT ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ hLT0 hLT 2
      _ = 9 * L ^ 2 := by ring
  have hP0 : 0 ≤ P := hQ0.trans hQP
  have e1 : B * LT ^ 2 ≤ 26000 * (9 * L ^ 2) := mul_le_mul hB hLT2 (sq_nonneg _) (by norm_num)
  have e2 : x * Q ≤ x * P := mul_le_mul_of_nonneg_left hQP hx0.le
  have e3 : 4 * (B * LT ^ 2) * (x * Q) ≤ 4 * (26000 * (9 * L ^ 2)) * (x * P) :=
    mul_le_mul (by linarith) e2 (by positivity) (by positivity)
  rw [div_le_iff₀ hT0]
  have hLP : 0 ≤ L ^ 2 * P := by positivity
  have e4 : 4 * (26000 * (9 * L ^ 2)) * (x * P) = 936000 * (L ^ 2 * P) * x := by ring
  have e5 : 936000 * (L ^ 2 * P) * x ≤ 937 * (L ^ 2 * P) * T := by
    have := mul_le_mul_of_nonneg_left hxT hLP
    nlinarith
  nlinarith

lemma num_left {A1 A2 L Q P : ℝ} (hA1 : A1 ≤ 4 * L) (hA2 : A2 ≤ 4 * L) (hA20 : 0 ≤ A2)
    (hL1 : 1 ≤ L) (hQ0 : 0 ≤ Q) (hQP : Q ≤ P) :
    (30 + 2 * A1) * (6 * Q) * (2 * A2) ≤ 1824 * L ^ 2 * P := by
  have e1 : 30 + 2 * A1 ≤ 38 * L := by linarith
  have e2 : 2 * A2 ≤ 8 * L := by linarith
  have e3 : (30 + 2 * A1) * (6 * Q) ≤ 38 * L * (6 * P) :=
    mul_le_mul e1 (by linarith) (by positivity) (by linarith)
  have hP0 : 0 ≤ P := hQ0.trans hQP
  have e4 := mul_le_mul e3 e2 (by positivity) (by positivity)
  nlinarith

lemma num_zero {LT L P : ℝ} (hLT0 : 0 ≤ LT) (hLT : LT ≤ 3 * L) (hL1 : 1 ≤ L) (hP1 : 1 ≤ P) :
    (P + 1) * (47 + 600 * LT ^ 2) ≤ 10894 * L ^ 2 * P := by
  have hLT2 : LT ^ 2 ≤ 9 * L ^ 2 := by
    calc LT ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ hLT0 hLT 2
      _ = 9 * L ^ 2 := by ring
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have e1 : 47 + 600 * LT ^ 2 ≤ 5447 * L ^ 2 := by nlinarith
  have e2 : (P + 1) * (47 + 600 * LT ^ 2) ≤ (2 * P) * (5447 * L ^ 2) :=
    mul_le_mul (by linarith) e1 (by positivity) (by positivity)
  nlinarith

lemma num_combine {a b z p hb ht hl P Q L : ℝ} (hP1 : 1 ≤ P) (hQP : Q ≤ P) (hL1 : 1 ≤ L)
    (ha : a ≤ 27 * Q) (hb' : b ≤ 1) (hz : z ≤ 10894 * L ^ 2 * P) (hp : p ≤ 2)
    (hbot : hb ≤ 937 * L ^ 2 * P) (htop : ht ≤ 937 * L ^ 2 * P) (hleft : hl ≤ 1824 * L ^ 2 * P) :
    a + b + z + p + (hb + ht + hl) / (2 * π) ≤ 11600 * P * L ^ 2 := by
  have hpi3 := Real.pi_gt_three
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hLP : P ≤ L ^ 2 * P := by nlinarith
  have hs : hb + ht + hl ≤ 3698 * (L ^ 2 * P) := by linarith
  have hd : (hb + ht + hl) / (2 * π) ≤ 3698 * (L ^ 2 * P) / 6 := by
    rcases le_or_gt (hb + ht + hl) 0 with h | h
    · have : (hb + ht + hl) / (2 * π) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (by positivity)
      have : 0 ≤ 3698 * (L ^ 2 * P) / 6 := by positivity
      linarith
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
  nlinarith

/-- `T = heights (N² + N)` lies in `[x², x³]` for `x = N + 1/2`, `N ≥ 999`. -/
lemma heights_bounds {N : ℕ} (hN : 999 ≤ N) :
    ((N : ℝ) + 1 / 2) ^ 2 ≤ HorizontalVanishingSeq.heights (N * N + N) ∧
      HorizontalVanishingSeq.heights (N * N + N) ≤ ((N : ℝ) + 1 / 2) ^ 3 ∧
      999 * ((N : ℝ) + 1 / 2) ≤ HorizontalVanishingSeq.heights (N * N + N) := by
  have hN' : (999 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 := HorizontalVanishingSeq.heights_ge (N * N + N)
  have h2 := HorizontalVanishingSeq.heights_le (N * N + N)
  push_cast at h1 h2
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **Half-integers.** Under quasi-RH, for `N ≥ 999` and `x = N + 1/2`:
`|ψ(x) − x| ≤ 11600 x^{7/8} log² x`. -/
theorem psi_halfint_explicit_of_quasiRH (hQ : QuasiRHWiring.QuasiRH) {N : ℕ} (hN : 999 ≤ N) :
    |Chebyshev.psi ((N : ℝ) + 1 / 2) - ((N : ℝ) + 1 / 2)| ≤
      11600 * ((N : ℝ) + 1 / 2) ^ (7 / 8 : ℝ) * Real.log ((N : ℝ) + 1 / 2) ^ 2 := by
  have hN1 : 1 ≤ N := by omega
  have hN' : (999 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hTx2, hTx3, hxT⟩ := heights_bounds hN
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hk2 : 2 ≤ N * N + N := by nlinarith
  set T : ℝ := HorizontalVanishingSeq.heights (N * N + N) with hTdef
  have hT4 : 4 ≤ T := by nlinarith
  have hT0 : 0 < T := by linarith
  -- the contour identity
  have hId := PsiContourProbe.contour_identity_of_continuous (a := Real.log x) continuous_g0
    (N * N + N) hk2
  rw [← hTdef] at hId
  have hmain := contour_algebra (ψ := ((Chebyshev.psi x : ℝ) : ℂ)) hId
    (right_edge_eq hx0 hT0.le) (Gt_g0_one hx0)
  -- logarithms
  set L : ℝ := Real.log x with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hx0]; linarith [Real.exp_one_lt_d9]
  have hLT : Real.log T ≤ 3 * L := by
    have := Real.log_le_log hT0 hTx3
    rwa [Real.log_pow, show ((3 : ℕ) : ℝ) = 3 by norm_num] at this
  have hLT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hx34 : x ^ 3 ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx4 : 5 / 2 + T ≤ x ^ 4 := by nlinarith
  have hL52 : Real.log (5 / 2 + T) ≤ 4 * L := by
    have := Real.log_le_log (by linarith) hx4
    rwa [Real.log_pow, show ((4 : ℕ) : ℝ) = 4 by norm_num] at this
  have hL1T : Real.log (1 + T) ≤ 4 * L := by
    have := Real.log_le_log (by linarith) (show 1 + T ≤ x ^ 4 by linarith)
    rwa [Real.log_pow, show ((4 : ℕ) : ℝ) = 4 by norm_num] at this
  have hL1T0 : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
  -- powers of `x`
  set Q : ℝ := x ^ (1 / 2 : ℝ) with hQdef
  set P : ℝ := x ^ (7 / 8 : ℝ) with hPdef
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hx1 (by norm_num)
  have hQP : Q ≤ P := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hP1 : 1 ≤ P := hQ1.trans hQP
  have h32 : x ^ (3 / 2 : ℝ) = x * Q := by
    rw [hQdef, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_one]
  have h52 : x ^ (5 / 2 : ℝ) = x ^ 2 * Q := by
    rw [hQdef, show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_two]
  -- (1) Perron at half-integers
  have hb1 : ‖((Chebyshev.psi x : ℝ) : ℂ) - ∑' n : ℕ, (Λ n : ℂ) * kernel (x / n) (3 / 2) T‖ ≤
      27 * Q := by
    refine (perron_error_halfint hN1 hT0).trans ?_
    rw [h52]
    exact num_perron hT0 hTx2 (by linarith)
  -- (2) `x⁻¹`
  have hb2 : ‖(x : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    exact inv_le_one_of_one_le₀ hx1
  -- (3) zeros
  have hb3 := (zero_side_le hQ hx1 hT4).trans (num_zero hLT0 hLT hL1 hP1)
  -- (4) the reflected Perron sum
  have hb4 := (perron_small (by linarith : 1 < x) hT0).trans (num_small hT4 hL1)
  -- (5) horizontal edges
  have hB := FleetExplicitPNTBounds.B_le
  have hseg := HorizontalVanishingSeq.segment_bound_log_sq_top (N * N + N) hk2
  have hsegb := HorizontalVanishingSeq.segment_bound_log_sq_bot (N * N + N) hk2
  rw [← hTdef] at hseg hsegb
  have hB0 : 0 ≤ HorizontalVanishingSeq.B := by
    have h0 := (norm_nonneg _).trans (hseg 0 ⟨by norm_num, by norm_num⟩)
    have h1 : 0 < Real.log T ^ 2 := by
      have := HorizontalVanishingSeq.one_le_log_heights (N * N + N)
      rw [← hTdef] at this; positivity
    exact nonneg_of_mul_nonneg_left h0 h1
  have hM0 : 0 ≤ HorizontalVanishingSeq.B * Real.log T ^ 2 := by positivity
  have hedge := num_edge hB hLT0 hLT hx0 (by linarith) hQP hxT hT0
  have htop := horiz_edge_le hx1 hT0.ne' hM0 hseg
  have hbot := horiz_edge_le hx1 (T' := -T) (by linarith) hM0 hsegb
  rw [abs_neg, abs_of_pos hT0, h32] at hbot
  rw [abs_of_pos hT0, h32] at htop
  -- (6) left edge
  have hleft := (left_edge_le hx1 hT0.le).trans
    (num_left hL52 hL1T hL1T0 hL1 (by linarith) hQP)
  -- combine
  have hfin := hmain.trans (num_combine hP1 hQP hL1 hb1 hb2 hb3 hb4 (hbot.trans hedge)
    (htop.trans hedge) hleft)
  have hcast : ((Chebyshev.psi x : ℝ) : ℂ) - (x : ℂ) = ((Chebyshev.psi x - x : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hfin
  exact hfin

/-- **Explicit prime number theorem from quasi-RH.** If `ζ(s) ≠ 0` for `Re s > 7/8`, then
`|ψ(x) − x| ≤ 12000 x^{7/8} (log x)²` for every `x ≥ 1000`. -/
theorem psi_explicit_of_quasiRH : QuasiRHWiring.QuasiRH →
    ∀ x ≥ (1000 : ℝ), |Chebyshev.psi x - x| ≤ 12000 * x ^ (7 / 8 : ℝ) * Real.log x ^ 2 := by
  intro hQ x hx
  set N : ℕ := ⌊x⌋₊ with hNdef
  have hx0 : 0 ≤ x := by linarith
  have hN : 1000 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  set y : ℝ := (N : ℝ) + 1 / 2 with hy
  have hpsi : Chebyshev.psi x = Chebyshev.psi y := by
    have hfl : ⌊y⌋₊ = N := by
      rw [hy, Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
    unfold Chebyshev.psi
    rw [hfl]
  have h := psi_halfint_explicit_of_quasiRH hQ (N := N) (by omega)
  rw [← hy] at h
  have hyx : |y - x| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hy1 : 1 ≤ y := by
    have : (1000 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hy0 : 0 < y := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx0' : 0 < x := by linarith
  -- comparison `y ≤ (1001/1000) x`
  have hyle : y ≤ 1001 / 1000 * x := by linarith
  have hpow : y ^ (7 / 8 : ℝ) ≤ 1001 / 1000 * x ^ (7 / 8 : ℝ) := by
    calc y ^ (7 / 8 : ℝ) ≤ (1001 / 1000 * x) ^ (7 / 8 : ℝ) :=
          Real.rpow_le_rpow hy0.le hyle (by norm_num)
      _ = (1001 / 1000 : ℝ) ^ (7 / 8 : ℝ) * x ^ (7 / 8 : ℝ) :=
          Real.mul_rpow (by norm_num) hx0
      _ ≤ 1001 / 1000 * x ^ (7 / 8 : ℝ) := by
          gcongr
          calc (1001 / 1000 : ℝ) ^ (7 / 8 : ℝ) ≤ (1001 / 1000 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 1001 / 1000 := Real.rpow_one _
  have hLx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0']; linarith [Real.exp_one_lt_d9]
  have hlog : Real.log y ≤ 1001 / 1000 * Real.log x := by
    have h1 : Real.log y ≤ Real.log (1001 / 1000 * x) := Real.log_le_log hy0 hyle
    rw [Real.log_mul (by norm_num) hx0'.ne'] at h1
    have h2 : Real.log (1001 / 1000 : ℝ) ≤ 1 / 1000 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1001 / 1000)
      linarith
    linarith
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hlog2 : Real.log y ^ 2 ≤ (1001 / 1000) ^ 2 * Real.log x ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hlogy0 hlog 2
  set P := x ^ (7 / 8 : ℝ) with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow hx1 (by norm_num)
  have hyP0 : 0 ≤ y ^ (7 / 8 : ℝ) := by positivity
  have hcomb : y ^ (7 / 8 : ℝ) * Real.log y ^ 2 ≤
      (1001 / 1000 * P) * ((1001 / 1000) ^ 2 * Real.log x ^ 2) :=
    mul_le_mul hpow hlog2 (sq_nonneg _) (by positivity)
  have hLL : 1 ≤ Real.log x ^ 2 := by nlinarith
  calc |Chebyshev.psi x - x| = |(Chebyshev.psi y - y) + (y - x)| := by rw [hpsi]; ring_nf
    _ ≤ |Chebyshev.psi y - y| + |y - x| := abs_add_le _ _
    _ ≤ 11600 * y ^ (7 / 8 : ℝ) * Real.log y ^ 2 + 1 / 2 := add_le_add h hyx
    _ ≤ 12000 * P * Real.log x ^ 2 := by nlinarith

end FleetExplicitPNT
