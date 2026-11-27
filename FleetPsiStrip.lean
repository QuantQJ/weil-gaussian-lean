import FleetPsiStripPerron
import FleetLandauTransfer
import PsiPrimeSide

/-!
# A zero strip gives `ψ(x) − x ≪ x^{1/2+δ+ε}`

If every nontrivial zero satisfies `|Re ρ − 1/2| ≤ δ` (`FleetHeadContour.StripBound δ`, `0 ≤ δ < 1/2`),
then for every `ε > 0`, `|ψ(x) − x| ≤ C x^{1/2+δ+ε}` for `x ≥ 2`. Here `ψ` is Mathlib's
`Chebyshev.psi x = ∑_{0 < n ≤ x} Λ(n)`; hp-proof's own `PsiPrimeSide.psi y = ∑_{n ≤ y} Λ(n)` is the same
function (`psiPrimeSide_eq_chebyshev_psi`).

The argument is the one of `FleetLandauTransfer.landauTransfer` (Möbius sums; adapted there from
kerr-lean `Kerr/Zeta/Littlewood.lean`, James C. Kerr, Apache-2.0), run on the coefficients
`Λ(n) − 1` instead of `μ(n)`:

* The Dirichlet series of `Λ(n) − 1` is `G = −ζ'/ζ − ζ` (Mathlib
  `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, `LSeries_zeta_eq_riemannZeta`). The poles of
  `−ζ'/ζ` and `ζ` at `s = 1` (both residue `1`) cancel, so `G` is holomorphic on `Re s > 1/2 + δ`
  (`psiG`, written through hp-proof's entire `FleetHeadContour.zetaReg`) and no residue has to be
  computed: the main term `x` comes from `∑_{n ≤ x} 1 = ⌊x⌋`.
* `logDeriv_zeta_le`: `‖ζ'/ζ(σ+it)‖ ≤ (14 log(9(|t|+4)) + 42)/δ²` for
  `σ ≥ 1/2 + δ₀ + 2δ`, `|t| ≥ 8`: the holomorphic `log ζ` on the zero-free disc of
  `FleetLandauTransfer.littlewood_aux` (`exists_log_ball`), the Borel–Carathéodory bound
  `‖log ζ‖ ≤ (14 log(9(|t|+4)) + 42)/δ` on the closed disc of radius `7/2 − δ` (the same estimate as
  in `littlewood_aux`), and the Cauchy estimate (Mathlib `norm_deriv_le_of_forall_mem_sphere_norm_le`)
  on a circle of radius `δ`.
* `psiG_bound`: `‖G(s)‖ ≤ C (1 + |Im s|)^η` on `Re s ≥ σ₀ > 1/2 + δ₀` (the `ζ` part is
  `FleetLandauTransfer.littlewood_bound`).
* `FleetPsiStrip.partial_sum_bound'` (coefficients `‖Λ(n) − 1‖ ≤ (1 + 1/κ) n^κ`) gives
  `|ψ(x) − ⌊x⌋| ≤ K x^{1/2+δ+ε}`.

Main results: `psi_error_of_stripBound`, `psi_error_of_quasiRH` (exponent `7/8 + ε`),
`psi_error_of_RH` (exponent `1/2 + ε`).
-/

noncomputable section
open Complex Metric Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt

namespace FleetPsiStrip

open FleetLandauTransfer

local notation "ζ" => riemannZeta

/-! ## 1. `ζ'/ζ` to the right of a zero-free half-plane -/

/-- **Log-derivative bound.** If `ζ ≠ 0` on `Re s > 1/2 + δ₀` (`δ₀ ≥ 0`), then for `δ > 0`,
`1/2 + δ₀ + 2δ ≤ σ ≤ 3 + δ₀` and `|t| ≥ 8`:
`‖ζ'(σ+it)/ζ(σ+it)‖ ≤ (14 log(9(|t|+4)) + 42)/δ/δ`. -/
theorem logDeriv_zeta_le {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → ζ s ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) {σ t : ℝ} (hσ1 : 1 / 2 + δ₀ + 2 * δ ≤ σ) (hσ2 : σ ≤ 3 + δ₀)
    (ht : 8 ≤ |t|) :
    ‖deriv ζ (σ + t * I) / ζ (σ + t * I)‖ ≤ (14 * Real.log (9 * (|t| + 4)) + 42) / δ / δ := by
  set c : ℂ := (4 + δ₀ : ℝ) + t * I with hc
  set R : ℝ := 7 / 2 - δ / 2 with hR
  set r₃ : ℝ := 7 / 2 - δ with hr₃
  have hRpos : 0 < R := by linarith
  have hball : ∀ z ∈ ball c R, 1 / 2 + δ₀ + δ / 2 < z.re ∧ |t| - 4 ≤ |z.im| ∧ |z.im| ≤ |t| + 4 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := abs_re_le_norm (z - c)
    have h2 := abs_im_le_norm (z - c)
    have e1 : (z - c).re = z.re - (4 + δ₀) := by simp [hc]
    have e2 : (z - c).im = z.im - t := by simp [hc]
    rw [e1] at h1
    rw [e2] at h2
    have a1 := (abs_lt.mp (h1.trans_lt hz)).1
    have a2 := abs_sub_abs_le_abs_sub z.im t
    have a3 := abs_sub_abs_le_abs_sub t z.im
    rw [abs_sub_comm] at a3
    refine ⟨by linarith, by linarith, by linarith⟩
  have hne1 : ∀ z ∈ ball c R, z ≠ 1 := by
    intro z hz h
    have := (hball z hz).2.1
    rw [h] at this; simp at this; linarith
  have hd : ∀ z ∈ ball c R, DifferentiableAt ℂ ζ z :=
    fun z hz => differentiableAt_riemannZeta (hne1 z hz)
  have hnz : ∀ z ∈ ball c R, ζ z ≠ 0 :=
    fun z hz => hZ z (by linarith [(hball z hz).1])
  obtain ⟨L, hLd, hLexp, hLc⟩ := exists_log_ball hd hnz hRpos
  have hcre : c.re = 4 + δ₀ := by simp [hc]
  have hLc3 : ‖L c‖ ≤ 3 := by rw [hLc]; exact log_zeta_norm_le (by rw [hcre]; linarith)
  -- Borel–Carathéodory
  set M := Real.log (9 * (|t| + 4)) with hM
  have hMpos : 0 < M := Real.log_pos (by linarith [abs_nonneg t])
  set g : ℂ → ℂ := fun z => L (c + z) with hg
  have hmemc : ∀ z ∈ ball (0 : ℂ) R, c + z ∈ ball c R := by
    intro z hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    simpa using hz
  have hgd : DifferentiableOn ℂ g (ball 0 R) := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun z : ℂ => c + z) z := (differentiableAt_id).const_add c
    exact ((hLd _ (hmemc z hz)).differentiableAt.comp z h1).differentiableWithinAt
  have hgM : MapsTo g (ball 0 R) {z | z.re ≤ M} := by
    intro z hz
    have hw := hmemc z hz
    simp only [mem_ofPred_eq, hg]
    have hre : (L (c + z)).re = Real.log ‖ζ (c + z)‖ := by
      rw [← hLexp _ hw, norm_exp, Real.log_exp]
    rw [hre]
    obtain ⟨h1, h2, h3⟩ := hball _ hw
    have hz9 := zeta_norm_le_poly (s := c + z) (by linarith) (by linarith)
    apply Real.log_le_log (norm_pos_iff.mpr (hnz _ hw))
    linarith
  have hBC : ∀ w, ‖w - c‖ ≤ r₃ → ‖L w‖ ≤ (14 * M + 42) / δ := by
    intro w hw
    have hz : w - c ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
    have key := borelCaratheodory hMpos hgd hgM hRpos hz
    simp only [hg, add_sub_cancel, add_zero] at key
    have hu0 := norm_nonneg (w - c)
    have hden : δ / 2 ≤ R - ‖w - c‖ := by linarith
    have hδ2 : 0 < δ / 2 := by positivity
    have t1 : 2 * M * ‖w - c‖ / (R - ‖w - c‖) ≤ 2 * M * (7 / 2) / (δ / 2) :=
      div_le_div₀ (by positivity) (by gcongr; linarith) hδ2 hden
    have t2 : ‖L c‖ * (R + ‖w - c‖) / (R - ‖w - c‖) ≤ 3 * 7 / (δ / 2) :=
      div_le_div₀ (by norm_num) (mul_le_mul hLc3 (by linarith) (by linarith) (by norm_num))
        hδ2 hden
    calc ‖L w‖ ≤ _ := key
      _ ≤ 2 * M * (7 / 2) / (δ / 2) + 3 * 7 / (δ / 2) := add_le_add t1 t2
      _ = (14 * M + 42) / δ := by field_simp; ring
  -- Cauchy estimate on the circle of radius `δ` about `s = σ + it`
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsc : ‖s - c‖ = 4 + δ₀ - σ := by
    have : s - c = ((σ - (4 + δ₀) : ℝ) : ℂ) := by rw [hs, hc]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hcl : closedBall s δ ⊆ ball c R := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    calc ‖z - c‖ ≤ ‖z - s‖ + ‖s - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < R := by rw [hsc]; linarith
  have hdc : DiffContOnCl ℂ L (ball s δ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hδ.ne']
    exact fun z hz => (hLd z (hcl hz)).differentiableAt.differentiableWithinAt
  have hsph : ∀ z ∈ sphere s δ, ‖L z‖ ≤ (14 * M + 42) / δ := by
    intro z hz
    apply hBC
    rw [mem_sphere, dist_eq_norm] at hz
    calc ‖z - c‖ ≤ ‖z - s‖ + ‖s - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ r₃ := by rw [hz, hsc]; linarith
  have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hdc hsph
  have hsR : s ∈ ball c R := hcl (mem_closedBall_self hδ.le)
  rw [(hLd s hsR).deriv] at key
  exact key

/-- **`ζ'/ζ ≪ |t|^η`** on `σ₀ ≤ σ ≤ 3 + δ₀`, `|t| ≥ 8`, when `ζ ≠ 0` on `Re s > 1/2 + δ₀` and
`σ₀ > 1/2 + δ₀`, for every `η > 0`. -/
theorem logDeriv_zeta_bound {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → ζ s ≠ 0)
    {σ₀ : ℝ} (hσ₀ : 1 / 2 + δ₀ < σ₀) {η : ℝ} (hη : 0 < η) :
    ∃ C > 0, ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 3 + δ₀ → 8 ≤ |t| →
      ‖deriv ζ (σ + t * I) / ζ (σ + t * I)‖ ≤ C * |t| ^ η := by
  set δ := (σ₀ - (1 / 2 + δ₀)) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set A := 14 * Real.log 18 + 42 + 14 / η with hA
  have hl18 : 0 ≤ Real.log 18 := Real.log_nonneg (by norm_num)
  refine ⟨A / δ / δ, by positivity, fun σ t hσ hσ2 ht => ?_⟩
  have key := logDeriv_zeta_le hδ₀ hZ hδ0 (by rw [hδ]; linarith) hσ2 ht
  refine key.trans ?_
  have ht0 : 0 < |t| := by linarith
  have hlog : Real.log (9 * (|t| + 4)) ≤ Real.log 18 + |t| ^ η / η := by
    have h1 : Real.log (9 * (|t| + 4)) ≤ Real.log (18 * |t|) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) ht0.ne'] at h1
    have h2 := Real.log_le_rpow_div (abs_nonneg t) hη
    linarith
  have h1 : 1 ≤ |t| ^ η := Real.one_le_rpow (by linarith) hη.le
  have hnum : 14 * Real.log (9 * (|t| + 4)) + 42 ≤ A * |t| ^ η := by
    calc 14 * Real.log (9 * (|t| + 4)) + 42 ≤ 14 * (Real.log 18 + |t| ^ η / η) + 42 := by
          linarith
      _ = (14 * Real.log 18 + 42) * 1 + 14 / η * |t| ^ η := by ring
      _ ≤ (14 * Real.log 18 + 42) * |t| ^ η + 14 / η * |t| ^ η := by gcongr
      _ = A * |t| ^ η := by rw [hA]; ring
  calc (14 * Real.log (9 * (|t| + 4)) + 42) / δ / δ ≤ A * |t| ^ η / δ / δ := by gcongr
    _ = A / δ / δ * |t| ^ η := by ring

/-! ## 2. The Dirichlet series of `Λ(n) − 1`: `−ζ'/ζ − ζ`, holomorphic at `s = 1` -/

/-- The coefficients `Λ(n) − 1` (`n ≥ 1`), `0` at `n = 0`. -/
def vmCoeff : ℕ → ℂ := fun n => (Λ n : ℂ) - ((ArithmeticFunction.zeta n : ℕ) : ℂ)

/-- `−ζ'/ζ − ζ`, completed at `s = 1`: with `R = zetaReg`,
`−((s−1)R'(s) + 2R(s) + (s−1)R(s)²)/((s−1)R(s) + 1)` (`= −ζ'/ζ − ζ` off `1` and the zeros). -/
def psiG (s : ℂ) : ℂ :=
  -((s - 1) * deriv FleetHeadContour.zetaReg s + 2 * FleetHeadContour.zetaReg s +
      (s - 1) * FleetHeadContour.zetaReg s ^ 2) / ((s - 1) * FleetHeadContour.zetaReg s + 1)

lemma psiG_alg {u R R' : ℂ} (hu : u ≠ 0) (hD : u * R + 1 ≠ 0) :
    -(u * R' + 2 * R + u * R ^ 2) / (u * R + 1) =
      -((R' - (u ^ 2)⁻¹) / (R + u⁻¹)) - (R + u⁻¹) := by
  have e : R + u⁻¹ = (u * R + 1) / u := by field_simp
  rw [e]
  field_simp
  ring

lemma psiG_eq {s : ℂ} (hs : s ≠ 1) (hz : ζ s ≠ 0) : psiG s = -(deriv ζ s / ζ s) - ζ s := by
  have hu : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hD : (s - 1) * FleetHeadContour.zetaReg s + 1 ≠ 0 := by
    rw [sub_one_mul_zeta hs]; exact mul_ne_zero hu hz
  rw [psiG, FleetHeadContour.deriv_riemannZeta_eq hs, FleetHeadContour.riemannZeta_eq_zetaReg hs]
  exact psiG_alg hu hD

lemma psiG_differentiableAt {s : ℂ} (hs : s = 1 ∨ ζ s ≠ 0) : DifferentiableAt ℂ psiG s := by
  have hden : (s - 1) * FleetHeadContour.zetaReg s + 1 ≠ 0 := by
    rcases hs with h | h
    · simp [h]
    · by_cases h1 : s = 1
      · simp [h1]
      · rw [sub_one_mul_zeta h1]; exact mul_ne_zero (sub_ne_zero.mpr h1) h
  have hd : DifferentiableAt ℂ FleetHeadContour.zetaReg s :=
    FleetHeadContour.differentiable_zetaReg s
  have hd' : DifferentiableAt ℂ (deriv FleetHeadContour.zetaReg) s :=
    (FleetHeadContour.differentiable_zetaReg.differentiableOn.deriv isOpen_univ).differentiableAt
      (isOpen_univ.mem_nhds (mem_univ s))
  have h1 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s := differentiableAt_id.sub_const 1
  exact ((((h1.mul hd').add (hd.const_mul 2)).add (h1.mul (hd.pow 2))).neg).div
    ((h1.mul hd).add_const 1) hden

theorem psiG_differentiableAt_of_zeroFree {δ₀ : ℝ}
    (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → ζ s ≠ 0) {s : ℂ} (hs : 1 / 2 + δ₀ < s.re) :
    DifferentiableAt ℂ psiG s :=
  psiG_differentiableAt (Or.inr (hZ s hs))

lemma vmCoeff_zero : vmCoeff 0 = 0 := by simp [vmCoeff]

/-- `G = L(Λ − 1, ·)` on `Re s > 1`. -/
lemma psiG_eq_LSeries {s : ℂ} (hs : 1 < s.re) : psiG s = LSeries vmCoeff s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hz : ζ s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  rw [psiG_eq hs1 hz]
  have e : vmCoeff =
      (fun n => (Λ n : ℂ)) - (fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) := rfl
  rw [e, LSeries_sub (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
    (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs),
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  ring

/-- `‖Λ(n) − 1‖ ≤ (1 + 1/κ) n^κ` (from `Λ(n) ≤ log n ≤ n^κ/κ`). -/
lemma norm_vmCoeff_le {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    ‖vmCoeff n‖ ≤ (1 + 1 / κ) * (n : ℝ) ^ κ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [vmCoeff_zero, norm_zero]; positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hz : ((ArithmeticFunction.zeta n : ℕ) : ℂ) = 1 := by
    simp [ArithmeticFunction.zeta_apply, hn.ne']
  have e : vmCoeff n = ((Λ n - 1 : ℝ) : ℂ) := by
    simp only [vmCoeff, hz]; push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have h0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have h2 := Real.log_le_rpow_div (Nat.cast_nonneg n) hκ
  have h3 : 1 ≤ (n : ℝ) ^ κ := Real.one_le_rpow hn1 hκ.le
  have e2 : (1 + 1 / κ) * (n : ℝ) ^ κ = (n : ℝ) ^ κ + (n : ℝ) ^ κ / κ := by ring
  have h4 : 0 ≤ (n : ℝ) ^ κ / κ := by positivity
  rw [e2, abs_le]
  constructor <;> linarith

/-! ## 3. `ψ` -/

/-- hp-proof's `PsiPrimeSide.psi` is Mathlib's `Chebyshev.psi`. -/
theorem psiPrimeSide_eq_chebyshev_psi (y : ℝ) : PsiPrimeSide.psi y = Chebyshev.psi y := by
  rw [PsiPrimeSide.psi, Chebyshev.psi_eq_sum_Icc]
  congr 1
  ext n
  simp only [Finset.mem_range, Finset.mem_Icc, zero_le, true_and]
  omega

/-- `∑_{n ≤ x} (Λ(n) − 1) = ψ(x) − ⌊x⌋`. -/
lemma sum_vmCoeff (x : ℝ) :
    ∑ n ∈ Finset.Iic ⌊x⌋₊, vmCoeff n = ((Chebyshev.psi x - (⌊x⌋₊ : ℝ) : ℝ) : ℂ) := by
  have hI : Finset.Iic ⌊x⌋₊ = Finset.range (⌊x⌋₊ + 1) := by
    ext n; simp only [Finset.mem_Iic, Finset.mem_range]; omega
  rw [hI, ← psiPrimeSide_eq_chebyshev_psi, PsiPrimeSide.psi]
  simp only [vmCoeff, Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ' (fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ))]
  simp [ArithmeticFunction.zeta_apply]

/-! ## 4. The bound for `G` and the main theorem -/

/-- **`‖−ζ'/ζ − ζ‖ ≪ (1 + |t|)^η`** on `Re s ≥ σ₀ > 1/2 + δ₀`, when `ζ ≠ 0` on `Re s > 1/2 + δ₀`. -/
theorem psiG_bound {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → ζ s ≠ 0)
    {σ₀ : ℝ} (hσ₀ : 1 / 2 + δ₀ < σ₀) {η : ℝ} (hη : 0 < η) :
    ∃ C > 0, ∀ s : ℂ, σ₀ ≤ s.re → ‖psiG s‖ ≤ C * (1 + |s.im|) ^ η := by
  obtain ⟨C₁, hC₁, hD⟩ := logDeriv_zeta_bound hδ₀ hZ hσ₀ hη
  obtain ⟨C₂, hC₂, hL⟩ := littlewood_bound hδ₀ hZ (δ := σ₀ - (1 / 2 + δ₀)) (by linarith) hη
  set S := ∑' n : ℕ, ExplicitFormula.coeff (1 + 1) n with hS
  have hK : IsCompact ((Icc σ₀ 2) ×ℂ (Icc (-8) 8)) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn psiG ((Icc σ₀ 2) ×ℂ (Icc (-8) 8)) := by
    intro z hz
    rw [mem_reProdIm] at hz
    exact (psiG_differentiableAt_of_zeroFree hZ
      (by linarith [hz.1.1])).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  set C := max (max (C₁ + C₂) M) (S + 2) with hC
  have hC12 : C₁ + C₂ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  refine ⟨C, lt_of_lt_of_le (by positivity) hC12, ?_⟩
  intro s hs
  have h1 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
  have hCpos : 0 ≤ C := le_trans (by positivity) hC12
  by_cases h2 : 2 ≤ s.re
  · have hs1 : s ≠ 1 := by intro h; rw [h] at h2; norm_num at h2
    have hz : ζ s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
    rw [psiG_eq hs1 hz]
    have ha := ZetaGrowth.norm_logDeriv_zeta_le_of_re_ge one_pos (s := s) (by linarith)
    have hb := zeta_norm_le_two h2
    calc ‖-(deriv ζ s / ζ s) - ζ s‖ ≤ ‖deriv ζ s / ζ s‖ + ‖ζ s‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_neg]
      _ ≤ S + 2 := add_le_add ha hb
      _ ≤ C := le_max_right _ _
      _ ≤ _ := le_mul_of_one_le_right hCpos h1
  push Not at h2
  by_cases h8 : |s.im| ≤ 8
  · have := hM s (by rw [mem_reProdIm]; exact ⟨⟨hs, h2.le⟩, abs_le.mp h8⟩)
    calc ‖psiG s‖ ≤ M := this
      _ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
      _ ≤ _ := le_mul_of_one_le_right hCpos h1
  push Not at h8
  have hs1 : s ≠ 1 := by intro h; rw [h] at h8; norm_num at h8
  have hz : ζ s ≠ 0 := hZ s (by linarith)
  rw [psiG_eq hs1 hz]
  have e : s = (s.re : ℂ) + (s.im : ℂ) * I := (re_add_im s).symm
  have ha := hD s.re s.im hs (by linarith) h8.le
  have hb := (hL s.re s.im (by linarith) h8.le).1
  rw [← e] at ha hb
  have hti : |s.im| ^ η ≤ (1 + |s.im|) ^ η :=
    Real.rpow_le_rpow (abs_nonneg _) (by linarith) hη.le
  calc ‖-(deriv ζ s / ζ s) - ζ s‖ ≤ ‖deriv ζ s / ζ s‖ + ‖ζ s‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_neg]
    _ ≤ C₁ * |s.im| ^ η + C₂ * |s.im| ^ η := add_le_add ha hb
    _ = (C₁ + C₂) * |s.im| ^ η := by ring
    _ ≤ C * (1 + |s.im|) ^ η := by gcongr

open FleetHeadContour in
/-- **Prime-counting consequence of a zero strip.** If every nontrivial zero has
`|Re ρ − 1/2| ≤ δ` (`0 ≤ δ < 1/2`), then for every `ε > 0` there is `C` with
`|ψ(x) − x| ≤ C x^{1/2+δ+ε}` for all `x ≥ 2` (`ψ = Chebyshev.psi`). -/
theorem psi_error_of_stripBound {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) (hs : StripBound δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ (1 / 2 + δ + ε) := by
  have hZ : ∀ s : ℂ, 1 / 2 + δ < s.re → ζ s ≠ 0 :=
    fun s hre => zeta_ne_zero_of_stripBound hδ hs hre
  set ε' := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨C, hC, hb⟩ := psiG_bound hδ hZ (σ₀ := 1 / 2 + δ + ε' / 2) (by linarith)
    (η := ε' / 2 / 2) (by positivity)
  set κ := ε' / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  set B := 1 + 1 / κ with hB
  have hB0 : 0 ≤ B := by positivity
  set K := 64 * (16 * C * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + ε' / 2 / 2))) + 6 * B with hK
  refine ⟨K + 1, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have key := partial_sum_bound' (a := vmCoeff) vmCoeff_zero hB0 (norm_vmCoeff_le hκ0)
    hκ0.le (by linarith) (G := psiG) (fun s hs => psiG_eq_LSeries hs)
    (σ₀ := 1 / 2 + δ + ε' / 2) (θ := ε' / 2)
    (by linarith) (by linarith) (by positivity) (by linarith) (by linarith) hC.le
    (fun s hs => psiG_differentiableAt_of_zeroFree hZ (by linarith)) hb hx1
  rw [← hK, sum_vmCoeff, Complex.norm_real, Real.norm_eq_abs] at key
  have hpow : x ^ (1 / 2 + δ + ε' / 2 + ε' / 2) ≤ x ^ (1 / 2 + δ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hone : 1 ≤ x ^ (1 / 2 + δ + ε) := Real.one_le_rpow hx1 (by linarith)
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + ε' / 2 / 2)) :=
      MeasureTheory.integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
    positivity
  have hfl : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [Nat.lt_floor_add_one x]
    · linarith [Nat.floor_le hx0.le]
  calc |Chebyshev.psi x - x| ≤ |Chebyshev.psi x - ⌊x⌋₊| + |(⌊x⌋₊ : ℝ) - x| :=
        abs_sub_le _ _ _
    _ ≤ K * x ^ (1 / 2 + δ + ε' / 2 + ε' / 2) + 1 := add_le_add key hfl
    _ ≤ K * x ^ (1 / 2 + δ + ε) + 1 * x ^ (1 / 2 + δ + ε) := by
        gcongr; linarith
    _ = (K + 1) * x ^ (1 / 2 + δ + ε) := by ring

/-- **Quasi-RH consequence.** If `ζ(s) ≠ 0` for `Re s > 7/8` (`QuasiRHWiring.QuasiRH`), then for every
`ε > 0`, `|ψ(x) − x| ≤ C x^{7/8+ε}` for `x ≥ 2`. -/
theorem psi_error_of_quasiRH (hQ : QuasiRHWiring.QuasiRH) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ (7 / 8 + ε) := by
  obtain ⟨C, hC⟩ := psi_error_of_stripBound (by norm_num) (by norm_num)
    (FleetHeadContour.stripBound_of_quasiRH hQ) hε
  refine ⟨C, fun x hx => ?_⟩
  have e : (1 : ℝ) / 2 + 3 / 8 + ε = 7 / 8 + ε := by ring
  rw [← e]
  exact hC x hx

/-- **RH consequence.** Under RH, for every `ε > 0`, `|ψ(x) − x| ≤ C x^{1/2+ε}` for `x ≥ 2`. -/
theorem psi_error_of_RH (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ (1 / 2 + ε) := by
  have hs : FleetHeadContour.StripBound 0 := fun ρ hρ => by
    rw [Reduction.riemannHypothesis_iff.mp hRH ρ hρ]; simp
  obtain ⟨C, hC⟩ := psi_error_of_stripBound le_rfl (by norm_num) hs hε
  refine ⟨C, fun x hx => ?_⟩
  have := hC x hx
  rwa [add_zero] at this

end FleetPsiStrip
