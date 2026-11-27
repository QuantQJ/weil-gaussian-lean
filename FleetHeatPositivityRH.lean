import FleetExponentLadder
import FleetSquareBank

/-!
# Heat positivity implies RH

`R_b(α) = Σ_ρ ĝ_{b,α}(γ_ρ)` (the Gaussian zero trace, equal to the arithmetic side by
`FleetPrimePoleBoundRH.zero_trace_eq_rhs`). Under RH every term is a positive Gaussian, so `Re R_b(α) ≥ 0`.

`ordinates_real_of_heat_positivity` proves the converse: if `Re R_b(α) ≥ 0` for every `0 < b ≤ 1` and every
real `α`, then every ordinate is real. An off-line zero `½ + e + iγ` contributes
`√(π/b) e^{(e² − (γ−α)²)/(4b)} cos(2(γ−α)e/(4b))` (with its partner); a small shift `α = α₀ + δ` off the
dominant height makes the dominant terms share one nonzero frequency, and at `s = 1/(4b)` where that cosine is
`−1` they outweigh everything else as `b → 0`.

`RH_iff_heat_positivity` : RH ⟺ `Re R_b(α) ≥ 0` for all `b ∈ (0,1]`, `α ∈ ℝ`; and the same with the arithmetic
side `rhs (gauss b α)` (`RH_iff_rhs_positivity`). This moves the heat-positivity criterion of
`research_notes/DUAL-INEQUALITY/HEAT_POSITIVITY.md` from paper (Tier E) to Lean.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set
open scoped Real
open OffLineDetection Reduction ZeroSumLimit GaussianTest

namespace FleetHeatPositivityRH

lemma re_gaussHat_polar {b : ℝ} (hb : 0 < b) (α : ℝ) (z : ℂ) {s : ℝ} (hs : s = 1 / (4 * b)) :
    (gaussHat b α z).re = Real.sqrt (π / b) * Real.exp (vE α z * s) * Real.cos (thetaE α z * s) := by
  rw [gaussHat_polar hb α z hs]
  have e : I * ((thetaE α z : ℝ) : ℂ) * (s : ℂ) = ((thetaE α z * s : ℝ) : ℂ) * I := by push_cast; ring
  rw [e, show (Real.sqrt (π / b) : ℂ) * ((Real.exp (vE α z * s) : ℝ) : ℂ)
      = ((Real.sqrt (π / b) * Real.exp (vE α z * s) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- Real-part estimate: with nonnegative real zero trace at `α` (for every `b ≤ 1`), a dominant set `S`
sharing `|θ| = ω` satisfies `−|S| cos(ω s) e^{M s} ≤ |Zfin α| e^{(M−ε)s} + C e^{−3s/4}`. -/
theorem re_key_estimate {α : ℝ} {S : Finset Index} (hSsub : S ⊆ Zfin α) {M ε C ω : ℝ}
    (hSM : ∀ x ∈ S, vE α (t x) = M)
    (hSθ : ∀ x ∈ S, |thetaE α (t x)| = ω)
    (hgap : ∀ x ∈ Zfin α, x ∉ S → vE α (t x) ≤ M - ε)
    (hC : ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, (Z α)ᶜ.indicator (fun x => gaussHat b α (t x)) x‖
        ≤ Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * C)
    (hpos : ∀ b : ℝ, 0 < b → b ≤ 1 → 0 ≤ (∑' x : Index, gaussHat b α (t x)).re)
    (s : ℝ) (hs : 1 / 4 ≤ s) :
    -((S.card : ℝ) * Real.cos (ω * s)) * Real.exp (M * s)
      ≤ (Zfin α).card * Real.exp ((M - ε) * s) + C * Real.exp (-(3 / 4) * s) := by
  classical
  set b : ℝ := 1 / (4 * s) with hb_def
  have hs0 : 0 < s := by linarith
  have hb : 0 < b := by positivity
  have hb1 : b ≤ 1 := by
    rw [hb_def, div_le_one (by positivity)]
    linarith
  have hsb : s = 1 / (4 * b) := by rw [hb_def]; field_simp
  have h316 : -3 / (16 * b) = -(3 / 4) * s := by rw [hb_def]; field_simp; ring
  have hsqrt : 0 < Real.sqrt (π / b) := Real.sqrt_pos.2 (div_pos Real.pi_pos hb)
  set f : Index → ℂ := fun x => gaussHat b α (t x) with hf_def
  have hfS : Summable f := (GaussianTraceFormula.gaussian_formula_zeros hb α).summable
  have hsplit := tsum_split α f hfS
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Real.sqrt (π / b) * Real.exp (M * s) * Real.cos (ω * s) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Real.sqrt (π / b) * Real.exp ((M - ε) * s) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  -- pointwise bound on the near sum
  have hpt : ∀ x ∈ Zfin α, (f x).re ≤ if x ∈ S then A else B := by
    intro x hx
    split_ifs with hxS
    · simp only [hf_def, hAdef]
      rw [re_gaussHat_polar hb α (t x) hsb, hSM x hxS]
      have hc : Real.cos (thetaE α (t x) * s) = Real.cos (ω * s) := by
        rw [← hSθ x hxS]
        rcases abs_choice (thetaE α (t x)) with h | h <;> rw [h]
        rw [neg_mul, Real.cos_neg]
      rw [hc]
    · have h1 := Complex.re_le_norm (f x)
      simp only [hf_def] at h1 ⊢
      rw [norm_gaussHat_s hb α (t x) hsb] at h1
      rw [hBdef]
      refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _))
      exact mul_le_mul_of_nonneg_right (hgap x hx hxS) hs0.le
  have hnear : (∑ x ∈ Zfin α, f x).re ≤ (S.card : ℝ) * A + (Zfin α).card * B := by
    rw [Complex.re_sum]
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hfilt : (Zfin α).filter (fun x => x ∈ S) = S := by
      ext x; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hSsub h, h⟩⟩
    rw [hfilt]
    have : (((Zfin α).filter (fun x => x ∉ S)).card : ℝ) ≤ (Zfin α).card := by
      exact_mod_cast Finset.card_filter_le _ _
    nlinarith
  have htail := hC b hb hb1
  rw [h316] at htail
  have h2 : (∑' x, (Z α)ᶜ.indicator f x).re ≤ ‖∑' x, (Z α)ᶜ.indicator f x‖ := by
    exact Complex.re_le_norm (∑' x, (Z α)ᶜ.indicator f x)
  have ht : (∑' x, (Z α)ᶜ.indicator f x).re ≤ Real.sqrt (π / b) * Real.exp (-(3 / 4) * s) * C :=
    h2.trans htail
  have hp := hpos b hb hb1
  change 0 ≤ (∑' x, f x).re at hp
  rw [hsplit, Complex.add_re] at hp
  have hkey : Real.sqrt (π / b) * (-((S.card : ℝ) * Real.cos (ω * s)) * Real.exp (M * s))
      ≤ Real.sqrt (π / b) * ((Zfin α).card * Real.exp ((M - ε) * s) + C * Real.exp (-(3 / 4) * s)) := by
    have e1 : Real.sqrt (π / b) * (-((S.card : ℝ) * Real.cos (ω * s)) * Real.exp (M * s)) = -((S.card : ℝ) * A) := by
      rw [hAdef]; ring
    have e2 : Real.sqrt (π / b) * ((Zfin α).card * Real.exp ((M - ε) * s) + C * Real.exp (-(3 / 4) * s))
        = (Zfin α).card * B + Real.sqrt (π / b) * Real.exp (-(3 / 4) * s) * C := by rw [hBdef]; ring
    rw [e1, e2]
    linarith
  exact le_of_mul_le_mul_left hkey hsqrt

set_option maxHeartbeats 4000000 in
/-- **Heat positivity ⇒ every ordinate is real.** -/
theorem ordinates_real_of_heat_positivity
    (hpos : ∀ b : ℝ, 0 < b → b ≤ 1 → ∀ α : ℝ, 0 ≤ (∑' x : Index, gaussHat b α (t x)).re) :
    ∀ x : Index, (t x).im = 0 := by
  classical
  intro x₀
  by_contra hβ
  set α₀ : ℝ := (t x₀).re with hα₀
  have hx₀ : x₀ ∈ Zfin α₀ := by rw [mem_Zfin, hα₀, sub_self, abs_zero]; exact one_pos
  -- dominant set at α₀
  obtain ⟨xm, hxm, hmax⟩ := Finset.exists_max_image (Zfin α₀) (fun x => vE α₀ (t x)) ⟨x₀, hx₀⟩
  obtain ⟨M₀, hM₀def⟩ : ∃ M₀ : ℝ, M₀ = vE α₀ (t xm) := ⟨_, rfl⟩
  rw [← hM₀def] at hmax
  have hM₀ : 0 < M₀ := by
    have h0 : vE α₀ (t x₀) = (t x₀).im ^ 2 := by simp only [vE, hα₀, sub_self]; ring
    have h1 : 0 < (t x₀).im ^ 2 := by positivity
    have := hmax x₀ hx₀; linarith
  set S₀ : Finset Index := (Zfin α₀).filter (fun x => vE α₀ (t x) = M₀)
  have hS₀sub : S₀ ⊆ Zfin α₀ := Finset.filter_subset _ _
  have hxmS₀ : xm ∈ S₀ := Finset.mem_filter.mpr ⟨hxm, hM₀def.symm⟩
  obtain ⟨ε₀, hε₀, hgap₀⟩ := exists_gap (Zfin α₀) (fun x => vE α₀ (t x)) M₀ (fun x hx => hmax x hx)
  -- among S₀, the largest offset d = Re − α₀
  obtain ⟨xd, hxd, hdmax⟩ := Finset.exists_max_image S₀ (fun x => (t x).re - α₀) ⟨xm, hxmS₀⟩
  obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = (t xd).re - α₀ := ⟨_, rfl⟩
  rw [← hddef] at hdmax
  set S₁ : Finset Index := S₀.filter (fun x => (t x).re - α₀ = d)
  have hS₁sub₀ : S₁ ⊆ S₀ := Finset.filter_subset _ _
  have hxdS₁ : xd ∈ S₁ := Finset.mem_filter.mpr ⟨hxd, hddef.symm⟩
  obtain ⟨η, hη, hgapd⟩ := exists_gap S₀ (fun x => (t x).re - α₀) d (fun x hx => hdmax x hx)
  -- offsets in S₀ are small
  have hoff : ∀ x ∈ S₀, ((t x).re - α₀) ^ 2 < 1 / 4 := by
    intro x hx
    have hv : vE α₀ (t x) = M₀ := (Finset.mem_filter.mp hx).2
    have := t_im_sq_lt x
    simp only [vE] at hv
    linarith
  have hd2 : d ^ 2 < 1 / 4 := by rw [hddef]; exact hoff xd hxd
  have hdabs : |d| < 1 / 2 := by
    rw [← abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    exact sq_lt_sq.mp (by norm_num; linarith)
  -- the shift δ
  obtain ⟨δ₀, hδ₀def⟩ : ∃ δ₀ : ℝ, δ₀ = min (1 / 8) (min (M₀ / 4) (ε₀ / 8)) := ⟨_, rfl⟩
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; exact lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hδ₀8 : δ₀ ≤ 1 / 8 := by rw [hδ₀def]; exact min_le_left _ _
  have hδ₀M : δ₀ ≤ M₀ / 4 := by rw [hδ₀def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ₀ε : δ₀ ≤ ε₀ / 8 := by rw [hδ₀def]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δ, hδpos, hδle, hδne⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ / 2 ∧ δ ≠ d := by
    by_cases h : δ₀ / 2 = d
    · exact ⟨δ₀ / 3, by positivity, by linarith, fun h' => by rw [← h'] at h; linarith⟩
    · exact ⟨δ₀ / 2, by positivity, le_rfl, h⟩
  have hδ8 : δ ≤ 1 / 16 := by linarith
  have hδM : δ ≤ M₀ / 8 := by linarith
  have hδε : δ ≤ ε₀ / 16 := by linarith
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = α₀ + δ := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = M₀ + 2 * δ * d - δ ^ 2 := ⟨_, rfl⟩
  have hdl := abs_lt.mp hdabs
  have hδd : δ * -(1 / 2) ≤ δ * d := mul_le_mul_of_nonneg_left hdl.1.le hδpos.le
  have hδsq : δ ^ 2 ≤ δ / 16 := by nlinarith
  have hMpos : 0 < M := by rw [hMdef]; nlinarith
  have hvshift : ∀ x : Index, vE α (t x) = vE α₀ (t x) + 2 * δ * ((t x).re - α₀) - δ ^ 2 := by
    intro x; simp only [vE]; rw [hαdef]; ring
  have hvS₁ : ∀ x ∈ S₁, vE α (t x) = M := by
    intro x hx
    have h1 := Finset.mem_filter.mp hx
    have h0 := (Finset.mem_filter.mp h1.1).2
    rw [hvshift, h0, h1.2, hMdef]
  have hS₁sub : S₁ ⊆ Zfin α := by
    intro x hx
    have h1 := (Finset.mem_filter.mp hx).2
    rw [mem_Zfin]
    have : (t x).re - α = d - δ := by rw [hαdef]; linarith
    rw [this, abs_lt]; constructor <;> linarith
  have hlt : ∀ x ∈ Zfin α, x ∉ S₁ → vE α (t x) < M := by
    intro x hxα hxS₁
    by_cases hx0 : x ∈ Zfin α₀
    · by_cases hxS₀ : x ∈ S₀
      · have hne : (t x).re - α₀ ≠ d := fun h => hxS₁ (Finset.mem_filter.mpr ⟨hxS₀, h⟩)
        have hle := hgapd x hxS₀ hne
        have h0 := (Finset.mem_filter.mp hxS₀).2
        rw [hvshift, h0, hMdef]
        have := mul_le_mul_of_nonneg_left hle hδpos.le
        nlinarith [mul_pos hδpos hη]
      · have hne : vE α₀ (t x) ≠ M₀ := fun h => hxS₀ (Finset.mem_filter.mpr ⟨hx0, h⟩)
        have hle := hgap₀ x hx0 hne
        have hd1 := abs_lt.mp (mem_Zfin.mp hx0)
        have := mul_le_mul_of_nonneg_left hd1.2.le hδpos.le
        rw [hvshift, hMdef]
        nlinarith
    · have hfar : 1 ≤ |(t x).re - α₀| := by
        by_contra h; push_neg at h; exact hx0 (mem_Zfin.mpr h)
      have him := t_im_sq_lt x
      have h3 : (t x).re - α = ((t x).re - α₀) - δ := by rw [hαdef]; ring
      have hge : 1 - δ ≤ |(t x).re - α| := by
        rw [h3]
        have := abs_sub_abs_le_abs_sub ((t x).re - α₀) δ
        rw [abs_of_pos hδpos] at this; linarith
      have h0 : 0 ≤ 1 - δ := by linarith
      have hsq : (1 - δ) ^ 2 ≤ ((t x).re - α) ^ 2 := by
        calc (1 - δ) ^ 2 ≤ |(t x).re - α| ^ 2 := pow_le_pow_left₀ h0 hge 2
          _ = ((t x).re - α) ^ 2 := sq_abs _
      have h15 : 1 / 4 < (1 - δ) ^ 2 := by
        have h1516 : (15 / 16 : ℝ) ≤ 1 - δ := by linarith
        have := pow_le_pow_left₀ (by norm_num) h1516 2
        linarith
      show (t x).im ^ 2 - ((t x).re - α) ^ 2 < M
      linarith
  obtain ⟨ε, hε, hgap⟩ := exists_gap (Zfin α) (fun x => vE α (t x)) M
    (fun x hx => by
      by_cases h : x ∈ S₁
      · exact le_of_eq (hvS₁ x h)
      · exact (hlt x hx h).le)
  have hgap' : ∀ x ∈ Zfin α, x ∉ S₁ → vE α (t x) ≤ M - ε := by
    intro x hx hxS
    exact hgap x hx (fun h => absurd h (ne_of_lt (hlt x hx hxS)))
  -- common frequency on S₁
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.sqrt (M₀ + d ^ 2) := ⟨_, rfl⟩
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ, ω = 2 * |d - δ| * E := ⟨_, rfl⟩
  have hθ : ∀ x ∈ S₁, |thetaE α (t x)| = ω := by
    intro x hx
    have h1 := Finset.mem_filter.mp hx
    have h0 := (Finset.mem_filter.mp h1.1).2
    have hre : (t x).re - α = d - δ := by rw [hαdef]; linarith [h1.2]
    have him : |(t x).im| = E := by
      have : (t x).im ^ 2 = M₀ + d ^ 2 := by
        simp only [vE] at h0; rw [h1.2] at h0; linarith
      rw [← Real.sqrt_sq_eq_abs, this, hEdef]
    simp only [thetaE]
    rw [hωdef, hre, abs_mul, abs_mul, him, abs_neg, _root_.abs_two]
  have hE : 0 < E := by rw [hEdef]; exact Real.sqrt_pos.2 (by nlinarith)
  have hω : 0 < ω := by
    have : 0 < |d - δ| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hδne))
    rw [hωdef]; positivity
  obtain ⟨C, hC0, hC⟩ := tail_bound α
  have hposα : ∀ b : ℝ, 0 < b → b ≤ 1 → 0 ≤ (∑' x : Index, gaussHat b α (t x)).re :=
    fun b hb hb1 => hpos b hb hb1 α
  -- the bound tends to 0
  have hB := tendsto_bound 0 (Zfin α).card C M ε hMpos hε
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hB.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  -- choose s with cos(ω s) = −1 and s ≥ max T (1/4)
  obtain ⟨k, hk⟩ := exists_nat_ge (max T (1 / 4) * ω / (2 * π))
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (2 * k + 1) * π / ω := ⟨_, rfl⟩
  have hs_ge : max T (1 / 4) ≤ s := by
    have hk' : max T (1 / 4) * ω ≤ (2 * k + 1) * π := by
      have := (div_le_iff₀ (by positivity : (0:ℝ) < 2 * π)).mp hk
      nlinarith [Real.pi_pos]
    rw [hsdef, le_div_iff₀ hω]; exact hk'
  have hcos : Real.cos (ω * s) = -1 := by
    have : ω * s = (2 * k + 1) * π := by rw [hsdef]; field_simp
    rw [this]
    have : (2 * (k : ℝ) + 1) * π = π + (k : ℕ) * (2 * π) := by ring
    rw [this, Real.cos_add_nat_mul_two_pi, Real.cos_pi]
  have hest := re_key_estimate hS₁sub hvS₁ hθ hgap' hC hposα s (le_trans (le_max_right _ _) hs_ge)
  rw [hcos] at hest
  have hcard : (1 : ℝ) ≤ S₁.card := by exact_mod_cast Finset.card_pos.mpr ⟨xd, hxdS₁⟩
  have hTs := hT s (le_trans (le_max_left _ _) hs_ge)
  have hexp : 0 < Real.exp (M * s) := Real.exp_pos _
  have e2 : Real.exp (-(ε * s)) * Real.exp (M * s) = Real.exp ((M - ε) * s) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (-((M + 3 / 4) * s)) * Real.exp (M * s) = Real.exp (-(3 / 4) * s) := by
    rw [← Real.exp_add]; congr 1; ring
  have : (S₁.card : ℝ) * Real.exp (M * s)
      ≤ ((Zfin α).card * Real.exp (-(ε * s)) + C * Real.exp (-((M + 3 / 4) * s))) * Real.exp (M * s) := by
    rw [add_mul, mul_assoc, e2, mul_assoc, e3]; linarith
  have hlt1 : (Zfin α).card * Real.exp (-(ε * s)) + C * Real.exp (-((M + 3 / 4) * s)) < 1 := by
    simpa using hTs
  nlinarith

/-- **RH from heat positivity.** -/
theorem RH_of_heat_positivity
    (hpos : ∀ b : ℝ, 0 < b → b ≤ 1 → ∀ α : ℝ, 0 ≤ (∑' x : Index, gaussHat b α (t x)).re) :
    RiemannHypothesis := by
  apply RH_of_nontrivial_zeros_on_critical_line
  intro ρ hρ
  obtain ⟨x, hx⟩ := multEnum_canonical.exists_index hρ
  have h := ordinates_real_of_heat_positivity hpos x
  rw [t_im, hx] at h
  linarith

/-- RH gives heat positivity: every term is `√(π/b) e^{-(γ−α)²/4b} > 0`. -/
theorem heat_positivity_of_RH (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 < b) (α : ℝ) :
    0 ≤ (∑' x : Index, gaussHat b α (t x)).re := by
  have h := FleetSquareBank.rhs_re_of_RH hRH hb α
  rw [show (∑' x : Index, gaussHat b α (t x)) = FleetFullLineArithmetic.rhs (gauss b α) from
    FleetPrimePoleBoundRH.zero_trace_eq_rhs hb α, h.2]
  exact tsum_nonneg (fun x => by unfold RealSideBound.term; positivity)

/-- **RH ⟺ heat positivity of the zero trace.** -/
theorem RH_iff_heat_positivity :
    RiemannHypothesis ↔ ∀ b : ℝ, 0 < b → b ≤ 1 → ∀ α : ℝ, 0 ≤ (∑' x : Index, gaussHat b α (t x)).re :=
  ⟨fun h b hb _ α => heat_positivity_of_RH h hb α, RH_of_heat_positivity⟩

/-- **RH ⟺ the arithmetic side of every Gaussian has nonnegative real part.** No zeros in the statement. -/
theorem RH_iff_rhs_positivity :
    RiemannHypothesis ↔ ∀ b : ℝ, 0 < b → b ≤ 1 → ∀ α : ℝ,
      0 ≤ (FleetFullLineArithmetic.rhs (gauss b α)).re := by
  rw [RH_iff_heat_positivity]
  constructor
  · intro h b hb hb1 α
    rw [← FleetPrimePoleBoundRH.zero_trace_eq_rhs hb α]; exact h b hb hb1 α
  · intro h b hb hb1 α
    have := h b hb hb1 α
    rw [← FleetPrimePoleBoundRH.zero_trace_eq_rhs hb α] at this; exact this

end FleetHeatPositivityRH
