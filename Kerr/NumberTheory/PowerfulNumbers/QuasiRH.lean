/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import Kerr.Zeta.Littlewood

/-!
# Quasi-RH ⇒ Littlewood bounds for `1/ζ` and `M(x) = O(x^{σ₀+ε})`

New file (written for this repo). `QuasiRH σ₀` says that `ζ(s) ≠ 0` for `Re s > σ₀`. The
statement `QuasiRH (7/8)` is the half-plane hypothesis attributed to an OpenAI preprint; it is
used here only as a named hypothesis (nothing in this repo proves or assumes it as an axiom).

The proofs below are the proofs of `Kerr.Littlewood.littlewood_aux`, `littlewood_bound`,
`invZeta_bound_RH` and `RH_implies_Mertens_growth` (same file layout and lemma names with a
`_quasi` suffix), with the RH input `ζ(s) ≠ 0` for `Re s > 1/2` replaced by `ζ(s) ≠ 0` for
`Re s > σ₀`: the disc of the Borel–Carathéodory step is now centred at `4 + it` with radius
`4 − σ₀ − δ/2` (it stays in `Re s > σ₀`), the three-circles radii are `1`, `4 − σ`,
`4 − σ₀ − δ`. Every other constant is unchanged.
-/

noncomputable section
open Complex Metric Set Filter Topology
open scoped ArithmeticFunction.Moebius

namespace Kerr.PowerfulNumbers

local notation "ζ" => riemannZeta

open Kerr.Littlewood

/-- **Quasi-Riemann hypothesis with exponent `σ₀`**: `ζ(s) ≠ 0` whenever `Re s > σ₀`.
`QuasiRH (1/2)` is RH; `QuasiRH (7/8)` is the half-plane statement of the OpenAI preprint
(credited; used only as a hypothesis). -/
def QuasiRH (σ₀ : ℝ) : Prop := ∀ s : ℂ, σ₀ < s.re → riemannZeta s ≠ 0

theorem quasiRH_of_RH (hRH : Kerr.File14RH.RiemannHypothesis') : QuasiRH (1 / 2) :=
  fun _ hs => zeta_ne_zero_of_RH hRH hs

theorem QuasiRH.mono {σ₀ σ₁ : ℝ} (h : QuasiRH σ₀) (h01 : σ₀ ≤ σ₁) : QuasiRH σ₁ :=
  fun s hs => h s (lt_of_le_of_lt h01 hs)

/-- Three-circles exponent for the quasi-RH geometry. -/
def thetaQ (σ₀ δ : ℝ) : ℝ := Real.log (4 - σ₀ - 2 * δ) / Real.log (4 - σ₀ - δ)

lemma thetaQ_mem {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ < 1) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) : 0 ≤ thetaQ σ₀ δ ∧ thetaQ σ₀ δ < 1 := by
  have h1 : 0 < Real.log (4 - σ₀ - 2 * δ) := Real.log_pos (by linarith)
  have h2 : Real.log (4 - σ₀ - 2 * δ) < Real.log (4 - σ₀ - δ) :=
    Real.log_lt_log (by linarith) (by linarith)
  exact ⟨div_nonneg h1.le (h1.trans h2).le, (div_lt_one (h1.trans h2)).mpr h2⟩

/-- **Littlewood's bound, explicit form, on a zero-free half-plane.** If `ζ ≠ 0` on `Re s > σ₀`,
then for `σ₀ + 2δ ≤ σ ≤ 3`, `|t| ≥ 8`: `‖ζ(σ+it)‖^{±1} ≤ exp (3 b^θ)`,
`b = (14 log(9(|t|+4)) + 42)/δ`, `θ = thetaQ σ₀ δ < 1`. -/
theorem littlewood_aux_quasi {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ < 1) (hQ : QuasiRH σ₀) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    {σ t : ℝ} (hσ1 : σ₀ + 2 * δ ≤ σ) (hσ2 : σ ≤ 3) (ht : 8 ≤ |t|) :
    ‖ζ (σ + t * I)‖ ≤ Real.exp (3 * ((14 * Real.log (9 * (|t| + 4)) + 42) / δ) ^ thetaQ σ₀ δ) ∧
    ‖ζ (σ + t * I)‖⁻¹ ≤ Real.exp (3 * ((14 * Real.log (9 * (|t| + 4)) + 42) / δ) ^ thetaQ σ₀ δ) := by
  set c : ℂ := 4 + t * I with hc
  set R : ℝ := 4 - σ₀ - δ / 2 with hR
  set r₃ : ℝ := 4 - σ₀ - δ with hr₃
  have hRpos : 0 < R := by linarith
  have hball : ∀ z ∈ ball c R, σ₀ + δ / 2 < z.re ∧ |t| - 4 ≤ |z.im| ∧ |z.im| ≤ |t| + 4 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := abs_re_le_norm (z - c)
    have h2 := abs_im_le_norm (z - c)
    have e1 : (z - c).re = z.re - 4 := by simp [hc]
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
    fun z hz => hQ z (by linarith [(hball z hz).1])
  obtain ⟨L, hLd, hLexp, hLc⟩ := exists_log_ball hd hnz hRpos
  have hsub2 : ball c 2 ⊆ ball c R := ball_subset_ball (by linarith)
  have hre2 : ∀ z ∈ ball c 2, 2 < z.re := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := abs_re_le_norm (z - c)
    have e1 : (z - c).re = z.re - 4 := by simp [hc]
    rw [e1] at h1
    linarith [(abs_lt.mp (h1.trans_lt hz)).1]
  have hLlog : ∀ z ∈ ball c 2, L z = Complex.log (ζ z) :=
    log_ball_eq_log two_pos (fun z hz => hd z (hsub2 hz)) (fun z hz => hLd z (hsub2 hz)) hLc
      (fun z hz => zeta_re_pos (hre2 z hz).le)
  have hcre : c.re = 4 := by simp [hc]
  have hLc3 : ‖L c‖ ≤ 3 := by rw [hLc]; exact log_zeta_norm_le (by rw [hcre]; norm_num)
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
  have hBC : ∀ w, ‖w - c‖ = r₃ → ‖L w‖ ≤ (14 * M + 42) / δ := by
    intro w hw
    have hz : w - c ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff, hw]; linarith
    have key := borelCaratheodory hMpos hgd hgM hRpos hz
    simp only [hg, add_sub_cancel, add_zero] at key
    rw [hw] at key
    have e : R - r₃ = δ / 2 := by rw [hR, hr₃]; ring
    rw [e] at key
    refine key.trans ?_
    have hLc0 : 0 ≤ ‖L c‖ := norm_nonneg _
    have e2 : 2 * M * r₃ / (δ / 2) + ‖L c‖ * (R + r₃) / (δ / 2) =
        (4 * M * r₃ + 2 * ‖L c‖ * (R + r₃)) / δ := by field_simp; ring
    rw [e2]
    apply div_le_div_of_nonneg_right _ hδ.le
    have hr3 : r₃ ≤ 7 / 2 := by linarith
    have hRr : R + r₃ ≤ 7 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hr3 hMpos.le, mul_le_mul_of_nonneg_left hRr hLc0]
  -- three circles
  have hcl : closedBall c r₃ ⊆ ball c R := closedBall_subset_ball (by linarith)
  have hf3 : ∀ z ∈ closedBall c r₃, DifferentiableAt ℂ L z :=
    fun z hz => (hLd z (hcl hz)).differentiableAt
  have ha : ∀ z, ‖z - c‖ = 1 → ‖L z‖ ≤ 3 := by
    intro z hz
    have hz2 : z ∈ ball c 2 := by rw [mem_ball, dist_eq_norm, hz]; norm_num
    rw [hLlog z hz2]
    exact log_zeta_norm_le (hre2 z hz2).le
  have hzc : ‖((σ : ℂ) + t * I) - c‖ = 4 - σ := by
    have : ((σ : ℂ) + t * I) - c = ((σ - 4 : ℝ) : ℂ) := by rw [hc]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have key := three_circles one_pos (by linarith : (1 : ℝ) < r₃) hf3 ha hBC
    (by rw [hzc]; linarith) (by rw [hzc]; linarith)
  rw [hzc, div_one, div_one] at key
  obtain ⟨hθ0, hθ1⟩ := thetaQ_mem hσ₀ hσ₀1 hδ hδ1
  set θ := Real.log (4 - σ) / Real.log r₃ with hθ
  have hlogr3 : 0 < Real.log r₃ := Real.log_pos (by linarith)
  have hθnn : 0 ≤ θ := div_nonneg (Real.log_nonneg (by linarith)) hlogr3.le
  have hθle : θ ≤ thetaQ σ₀ δ := by
    rw [hθ, thetaQ]
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) hlogr3.le
  set b := (14 * M + 42) / δ with hb
  have hb1 : 1 ≤ b := by
    rw [hb, le_div_iff₀ hδ]; linarith
  have hLz : ‖L (σ + t * I)‖ ≤ 3 * b ^ thetaQ σ₀ δ := by
    refine key.trans ?_
    have h3 : (3 : ℝ) ^ (1 - θ) ≤ 3 := by
      calc (3 : ℝ) ^ (1 - θ) ≤ 3 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 3 := Real.rpow_one 3
    have hbθ : b ^ θ ≤ b ^ thetaQ σ₀ δ := Real.rpow_le_rpow_of_exponent_le hb1 hθle
    exact mul_le_mul h3 hbθ (Real.rpow_nonneg (by linarith) _) (by norm_num)
  have hzR : ((σ : ℂ) + t * I) ∈ ball c R := hcl (by rw [mem_closedBall, dist_eq_norm, hzc]; linarith)
  have hn : ‖ζ (σ + t * I)‖ = Real.exp (L (σ + t * I)).re := by
    rw [← hLexp _ hzR, norm_exp]
  constructor
  · rw [hn]; exact Real.exp_le_exp.mpr ((re_le_norm _).trans hLz)
  · rw [hn, ← Real.exp_neg]
    refine Real.exp_le_exp.mpr ?_
    have := abs_re_le_norm (L (σ + t * I))
    have := neg_le_abs (L (σ + t * I)).re
    linarith

/-- **Littlewood's bound on a zero-free half-plane.** If `ζ` has no zeros in `Re s > σ₀`
(`1/2 ≤ σ₀ < 1`), then for every `δ > 0`, `η > 0` there is `C` with `‖ζ(σ+it)‖ ≤ C|t|^η` and
`‖ζ(σ+it)‖⁻¹ ≤ C|t|^η` for all `σ ≥ σ₀ + δ`, `|t| ≥ 8`. -/
theorem littlewood_bound_quasi {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ < 1) (hQ : QuasiRH σ₀) {δ : ℝ} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) :
    ∃ C > 0, ∀ σ t : ℝ, σ₀ + δ ≤ σ → 8 ≤ |t| →
      ‖ζ (σ + t * I)‖ ≤ C * |t| ^ η ∧ ‖ζ (σ + t * I)‖⁻¹ ≤ C * |t| ^ η := by
  set δ' := min (δ / 2) (1 / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min (by linarith) (by norm_num)
  have hδ'1 : δ' ≤ 1 / 2 := min_le_right _ _
  have hδ'2 : 2 * δ' ≤ δ := by have := min_le_left (δ / 2) (1 / 2); linarith
  obtain ⟨hθ0, hθ1⟩ := thetaQ_mem hσ₀ hσ₀1 hδ'0 hδ'1
  set θ := thetaQ σ₀ δ' with hθ
  set lam := η * δ' / 42 with hlam
  have hlam0 : 0 < lam := by positivity
  set K0 := lam ^ (-θ / (1 - θ)) with hK0
  set K := η * (Real.log 9 + 3) + 3 * K0 with hK
  set C := max 3 (Real.exp K * 2 ^ η) with hC
  refine ⟨C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro σ t hσ ht
  have ht1 : 1 ≤ |t| := by linarith
  have htη : 1 ≤ |t| ^ η := Real.one_le_rpow ht1 hη.le
  by_cases hσ2 : 2 ≤ σ
  · have hre : 2 ≤ ((σ : ℂ) + t * I).re := by simpa using hσ2
    have h1 := zeta_norm_le_two hre
    have h2 := zeta_norm_ge_third hre
    have hC3 : 3 ≤ C := le_max_left _ _
    constructor
    · nlinarith
    · have : ‖ζ (σ + t * I)‖⁻¹ ≤ 3 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      nlinarith
  push Not at hσ2
  have hσ' : σ₀ + 2 * δ' ≤ σ := by linarith
  obtain ⟨hA, hB⟩ := littlewood_aux_quasi hσ₀ hσ₀1 hQ hδ'0 hδ'1 hσ' (by linarith) ht
  -- bound the exponent
  set u := Real.log (|t| + 4) with hu
  have hu0 : 0 ≤ u := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog9 : Real.log (9 * (|t| + 4)) = Real.log 9 + u :=
    Real.log_mul (by norm_num) (by linarith [abs_nonneg t])
  set b := (14 * Real.log (9 * (|t| + 4)) + 42) / δ' with hb
  have hb0 : 0 ≤ b := by
    rw [hb]; apply div_nonneg _ hδ'0.le
    have : 0 ≤ Real.log (9 * (|t| + 4)) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hbθ := rpow_le_mul_add hθ0 hθ1 hb0 hlam0
  have hlog9pos : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hexpo : 3 * b ^ θ ≤ η * u + K := by
    have e : 3 * (lam * b) = η * u + η * (Real.log 9 + 3) := by
      rw [hlam, hb, hlog9]; field_simp; ring
    rw [hK]
    linarith
  have hE : Real.exp (3 * b ^ θ) ≤ Real.exp K * 2 ^ η * |t| ^ η := by
    calc Real.exp (3 * b ^ θ) ≤ Real.exp (η * u + K) := Real.exp_le_exp.mpr hexpo
      _ = Real.exp K * (|t| + 4) ^ η := by
          rw [Real.exp_add, Real.rpow_def_of_pos (by linarith [abs_nonneg t]), hu]; ring_nf
      _ ≤ Real.exp K * (2 * |t|) ^ η := by
          gcongr; linarith
      _ = Real.exp K * 2 ^ η * |t| ^ η := by
          rw [Real.mul_rpow (by norm_num) (abs_nonneg t)]; ring
  have hCK : Real.exp K * 2 ^ η * |t| ^ η ≤ C * |t| ^ η := by
    gcongr; exact le_max_right _ _
  exact ⟨hA.trans (hE.trans hCK), hB.trans (hE.trans hCK)⟩

open KerrPNT.Mobius in
theorem invZeta_differentiableAt_quasi {σ₀ : ℝ} (hQ : QuasiRH σ₀) {s : ℂ} (hs : σ₀ < s.re) :
    DifferentiableAt ℂ invZeta s := by
  by_cases h : s = 1
  · subst h; exact invZeta_differentiableAt_one
  · exact invZeta_differentiableAt_of_ne h (hQ s hs)

open KerrPNT.Mobius in
/-- Under `QuasiRH σ₀` (`1/2 ≤ σ₀ < 1`), for `σ₁ > σ₀` and `η > 0`:
`‖1/ζ(s)‖ ≤ C (1 + |Im s|)^η` on `Re s ≥ σ₁`. -/
theorem invZeta_bound_quasi {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ < 1) (hQ : QuasiRH σ₀)
    {σ₁ : ℝ} (hσ₁ : σ₀ < σ₁) {η : ℝ} (hη : 0 < η) :
    ∃ C > 0, ∀ s : ℂ, σ₁ ≤ s.re → ‖invZeta s‖ ≤ C * (1 + |s.im|) ^ η := by
  obtain ⟨C₁, hC₁, hL⟩ := littlewood_bound_quasi hσ₀ hσ₀1 hQ (δ := σ₁ - σ₀) (by linarith) hη
  have hK : IsCompact ((Icc σ₁ 2) ×ℂ (Icc (-8) 8)) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn invZeta ((Icc σ₁ 2) ×ℂ (Icc (-8) 8)) := by
    intro z hz
    rw [mem_reProdIm] at hz
    exact (invZeta_differentiableAt_quasi hQ (by linarith [hz.1.1])).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max (max C₁ M) 3, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro s hs
  have h1 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
  have hCpos : 0 ≤ max (max C₁ M) 3 := le_trans (by norm_num) (le_max_right _ _)
  by_cases h2 : 2 ≤ s.re
  · have hs1 : s ≠ 1 := by intro h; rw [h] at h2; norm_num at h2
    rw [invZeta_of_ne hs1, norm_inv]
    have h3 := zeta_norm_ge_third h2
    have : ‖ζ s‖⁻¹ ≤ 3 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc ‖ζ s‖⁻¹ ≤ 3 := this
      _ ≤ max (max C₁ M) 3 := le_max_right _ _
      _ ≤ _ := le_mul_of_one_le_right hCpos h1
  push Not at h2
  by_cases h8 : |s.im| ≤ 8
  · have := hM s (by rw [mem_reProdIm]; exact ⟨⟨hs, h2.le⟩, abs_le.mp h8⟩)
    calc ‖invZeta s‖ ≤ M := this
      _ ≤ max (max C₁ M) 3 := le_trans (le_max_right _ _) (le_max_left _ _)
      _ ≤ _ := le_mul_of_one_le_right hCpos h1
  push Not at h8
  have hs1 : s ≠ 1 := by intro h; rw [h] at h8; norm_num at h8
  rw [invZeta_of_ne hs1, norm_inv]
  have e : s = (s.re : ℂ) + (s.im : ℂ) * I := (re_add_im s).symm
  have := (hL s.re s.im (by linarith) h8.le).2
  rw [← e] at this
  calc ‖ζ s‖⁻¹ ≤ C₁ * |s.im| ^ η := this
    _ ≤ max (max C₁ M) 3 * (1 + |s.im|) ^ η := by
        gcongr
        · exact le_trans (le_max_left _ _) (le_max_left _ _)
        · linarith

open KerrPNT.Mobius in
/-- **Quasi-RH ⇒ `M(x) = O(x^{σ₀+ε})`.** If `ζ ≠ 0` on `Re s > σ₀` (`1/2 ≤ σ₀ < 1`), then for
every `ε > 0` there is `K` with `|∑_{n ≤ x} μ(n)| ≤ K x^{σ₀+ε}` for all `x ≥ 1`. -/
theorem mertens_bound_quasi {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ < 1) (hQ : QuasiRH σ₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K > 0, ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ)| ≤ K * x ^ (σ₀ + ε) := by
  set ε' := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨C, hC, hb⟩ := invZeta_bound_quasi hσ₀ hσ₀1 hQ (σ₁ := σ₀ + ε' / 2) (by linarith)
    (η := ε' / 2 / 2) (by positivity)
  set K := 64 * (16 * C * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + ε' / 2 / 2))) + 2 with hK
  have hI0 : 0 ≤ ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + ε' / 2 / 2)) :=
    MeasureTheory.integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  refine ⟨K, by positivity, fun x hx => ?_⟩
  have key := partial_sum_bound (a := fun n => (μ n : ℂ)) (by simp)
    (fun n => by rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
    (G := invZeta) (fun s hs => invZeta_eq_LSeries hs) (σ₀ := σ₀ + ε' / 2) (θ := ε' / 2)
    (by linarith) (by linarith) (by positivity) (by linarith) hC.le
    (fun s hs => invZeta_differentiableAt_quasi hQ (by linarith)) hb hx
  rw [← hK] at key
  have hM : |∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ)| = ‖∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℂ)‖ := by
    have e : (((∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ)) : ℝ) : ℂ) = ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℂ) := by
      push_cast; rfl
    rw [← e, Complex.norm_real, Real.norm_eq_abs]
  rw [hM]
  refine key.trans ?_
  have : x ^ (σ₀ + ε' / 2 + ε' / 2) ≤ x ^ (σ₀ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  gcongr

end Kerr.PowerfulNumbers
