/-
Kerr/PNT/MobiusInvZeta.lean — new file (written for this repo, not copied).
Bounds for 1/ζ in the classical zero-free region, built on the copied PrimeNumberTheoremAnd
results (`ZetaInvBnd`, `ZetaInvBound2`, `ZetaZeroFree1`, `ZetaNoZerosInBox`,
`LogDerivZetaUniformLogSquaredBound`; Apache-2.0, © the PrimeNumberTheoremAnd contributors).
-/
import Kerr.PNT.StrongPNT

open Complex Filter Topology Set

namespace KerrPNT.Mobius

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

/-- Mean-value step: along a horizontal segment where `ζ ≠ 0` and `‖ζ'/ζ‖ ≤ K`,
`‖ζ(1+it)‖ ≤ ‖ζ(σ+it)‖ · exp(K (1-σ))`. -/
lemma norm_zeta_one_le {t σ K : ℝ} (hσ : σ ≤ 1)
    (hne : ∀ u ∈ Icc σ 1, ζ (u + t * I) ≠ 0 ∧ (u : ℂ) + t * I ≠ 1)
    (hb : ∀ u ∈ Icc σ 1, ‖ζ' (u + t * I) / ζ (u + t * I)‖ ≤ K) :
    ‖ζ (1 + t * I)‖ ≤ ‖ζ (σ + t * I)‖ * Real.exp (K * (1 - σ)) := by
  set w : ℝ → ℂ := fun u ↦ ζ (u + t * I) with hw
  have hderw : ∀ u ∈ Icc σ 1, HasDerivAt w (ζ' (u + t * I)) u := by
    intro u hu
    have h1 : HasDerivAt (fun u : ℝ ↦ (u : ℂ) + t * I) 1 u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).add_const (t * I)
    have h2 : HasDerivAt ζ (ζ' (u + t * I)) ((fun u : ℝ ↦ (u : ℂ) + t * I) u) :=
      (differentiableAt_riemannZeta (hne u hu).2).hasDerivAt
    have h3 := h2.comp u h1
    rw [mul_one] at h3
    exact h3
  set φ : ℝ → ℝ := fun u ↦ Real.log (‖w u‖ ^ 2) with hφ
  set φ' : ℝ → ℝ := fun u ↦ (2 * inner ℝ (w u) (ζ' (u + t * I))) / ‖w u‖ ^ 2 with hφ'
  have hderφ : ∀ u ∈ Icc σ 1, HasDerivAt φ (φ' u) u := by
    intro u hu
    have hpos : ‖w u‖ ^ 2 ≠ 0 := by
      have := (hne u hu).1
      positivity
    exact ((hderw u hu).norm_sq).log hpos
  have hbφ : ∀ u ∈ Ico σ 1, ‖φ' u‖ ≤ 2 * K := by
    intro u hu
    have hu' : u ∈ Icc σ 1 := Ico_subset_Icc_self hu
    have hwne : w u ≠ 0 := (hne u hu').1
    have hwpos : 0 < ‖w u‖ := norm_pos_iff.mpr hwne
    have hin : |inner ℝ (w u) (ζ' (u + t * I))| ≤ ‖w u‖ * ‖ζ' (u + t * I)‖ :=
      abs_real_inner_le_norm _ _
    have hq : ‖ζ' (u + t * I)‖ / ‖w u‖ ≤ K := by
      have := hb u hu'
      rwa [norm_div] at this
    rw [Real.norm_eq_abs, hφ', abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_pos (by positivity : 0 < ‖w u‖ ^ 2), div_le_iff₀ (by positivity)]
    calc 2 * |inner ℝ (w u) (ζ' (u + t * I))| ≤ 2 * (‖w u‖ * ‖ζ' (u + t * I)‖) := by gcongr
      _ = 2 * (‖ζ' (u + t * I)‖ / ‖w u‖) * ‖w u‖ ^ 2 := by field_simp
      _ ≤ 2 * K * ‖w u‖ ^ 2 := by gcongr
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := φ) (fun u hu ↦ (hderφ u hu).hasDerivWithinAt) hbφ 1 ⟨hσ, le_rfl⟩
  rw [Real.norm_eq_abs] at hmvt
  have hle : φ 1 ≤ φ σ + 2 * K * (1 - σ) := by linarith [le_abs_self (φ 1 - φ σ)]
  have hw1 : w 1 ≠ 0 := (hne 1 ⟨hσ, le_rfl⟩).1
  have hwσ : w σ ≠ 0 := (hne σ ⟨le_rfl, hσ⟩).1
  have hexp := Real.exp_le_exp.mpr hle
  rw [Real.exp_add, hφ] at hexp
  simp only at hexp
  rw [Real.exp_log (by positivity), Real.exp_log (by positivity)] at hexp
  have hsq : ‖w 1‖ ^ 2 ≤ (‖w σ‖ * Real.exp (K * (1 - σ))) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    convert hexp using 3
    push_cast; ring
  have := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num : (2:ℕ) ≠ 0)).mp hsq
  simpa [hw] using this

lemma log_abs_gt_one {t : ℝ} (ht : 3 < |t|) : 1 < Real.log |t| := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith [Real.exp_one_lt_d9]

/-- `1/‖ζ(σ+it)‖ ≪ log^7 |t|` for `σ ∈ [1,2]`, `|t| > 3`. -/
lemma inv_norm_zeta_le_one_two :
    ∃ C > 0, ∀ σ ∈ Icc (1 : ℝ) 2, ∀ t : ℝ, 3 < |t| →
      1 / ‖ζ (σ + t * I)‖ ≤ C * Real.log |t| ^ (7 : ℝ) := by
  obtain ⟨A, hA, C1, hC1, h1⟩ := ZetaInvBnd
  obtain ⟨C2, hC2, h2⟩ := ZetaInvBound2
  refine ⟨max C1 (C2 * A ^ (-(3 : ℝ) / 4)), lt_max_of_lt_left hC1, ?_⟩
  intro σ hσ t ht
  have hL := log_abs_gt_one ht
  have hL0 : 0 < Real.log |t| := by linarith
  have hL9 : 0 < Real.log |t| ^ (9 : ℝ) := by positivity
  have hL7 : 0 < Real.log |t| ^ (7 : ℝ) := by positivity
  by_cases hc : σ < 1 + A / Real.log |t| ^ (9 : ℝ)
  · have hlow : 1 - A / Real.log |t| ^ (9 : ℝ) ≤ σ := by
      have : 0 < A / Real.log |t| ^ (9 : ℝ) := div_pos hA.1 hL9
      linarith [hσ.1]
    calc 1 / ‖ζ (σ + t * I)‖ ≤ C1 * Real.log |t| ^ (7 : ℝ) := h1 σ t ht ⟨hlow, hc⟩
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · push Not at hc
    have hσ1 : 1 < σ := lt_of_lt_of_le (by have := div_pos hA.1 hL9; linarith) hc
    have hd : A / Real.log |t| ^ (9 : ℝ) ≤ σ - 1 := by linarith
    have hpos : 0 < A / Real.log |t| ^ (9 : ℝ) := div_pos hA.1 hL9
    have key := h2 ⟨hσ1, hσ.2⟩ t ht
    have hmono : (σ - 1) ^ (-(3 : ℝ) / 4) ≤ (A / Real.log |t| ^ (9 : ℝ)) ^ (-(3 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos hpos hd (by norm_num)
    have heq : (A / Real.log |t| ^ (9 : ℝ)) ^ (-(3 : ℝ) / 4) * Real.log |t| ^ ((1 : ℝ) / 4)
        = A ^ (-(3 : ℝ) / 4) * Real.log |t| ^ (7 : ℝ) := by
      rw [Real.div_rpow hA.1.le hL9.le, ← Real.rpow_mul hL0.le, div_eq_mul_inv,
        ← Real.rpow_neg hL0.le, mul_assoc, ← Real.rpow_add hL0]
      norm_num
    calc 1 / ‖ζ (σ + t * I)‖ ≤ C2 * (σ - 1) ^ (-(3 : ℝ) / 4) * Real.log |t| ^ ((1 : ℝ) / 4) := key
      _ ≤ C2 * (A / Real.log |t| ^ (9 : ℝ)) ^ (-(3 : ℝ) / 4) * Real.log |t| ^ ((1 : ℝ) / 4) := by
          gcongr
      _ = C2 * A ^ (-(3 : ℝ) / 4) * Real.log |t| ^ (7 : ℝ) := by rw [mul_assoc, heq, mul_assoc]
      _ ≤ _ := by gcongr; exact le_max_right _ _

lemma log_pow_seven_le {t : ℝ} (ht : 1 ≤ |t|) :
    Real.log |t| ^ (7 : ℝ) ≤ 14 ^ 7 * |t| ^ ((1 : ℝ) / 2) := by
  have hL0 : 0 ≤ Real.log |t| := Real.log_nonneg ht
  have h1 : Real.log |t| ≤ |t| ^ ((1 : ℝ) / 14) / (1 / 14) :=
    Real.log_le_rpow_div (abs_nonneg t) (by norm_num)
  rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc Real.log |t| ^ 7 ≤ (|t| ^ ((1 : ℝ) / 14) / (1 / 14)) ^ 7 := by gcongr
    _ = 14 ^ 7 * |t| ^ ((1 : ℝ) / 2) := by
      rw [div_pow, ← Real.rpow_natCast (|t| ^ ((1 : ℝ) / 14)) 7,
        ← Real.rpow_mul (abs_nonneg t)]
      norm_num
      ring

/-- Main region bound: there are `η > 0`, `C > 0` with `ζ(σ+it) ≠ 0` and
`1/‖ζ(σ+it)‖ ≤ C |t|` for `|t| > 3`, `1 - η/log|t| ≤ σ ≤ 2`. -/
lemma inv_norm_zeta_le_strip :
    ∃ η > 0, ∃ C > 0, ∀ t : ℝ, 3 < |t| → ∀ σ ∈ Icc (1 - η / Real.log |t|) 2,
      ζ (σ + t * I) ≠ 0 ∧ 1 / ‖ζ (σ + t * I)‖ ≤ C * |t| := by
  obtain ⟨C7, hC7, h7⟩ := inv_norm_zeta_le_one_two
  obtain ⟨Cd, hCd, hd⟩ := LogDerivZetaUniformLogSquaredBound
  obtain ⟨A₁, hA₁, hfree⟩ := ZetaZeroFree1
  have hF : 0 < F := FinIoo.1
  set η := min (min A₁ F) (1 / (2 * Cd)) with hη
  have hηpos : 0 < η := lt_min (lt_min hA₁.1 hF) (by positivity)
  have hηA : η ≤ A₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hηF : η ≤ F := (min_le_left _ _).trans (min_le_right _ _)
  have hηC : Cd * η ≤ 1 / 2 := by
    have : η ≤ 1 / (2 * Cd) := min_le_right _ _
    calc Cd * η ≤ Cd * (1 / (2 * Cd)) := by gcongr
      _ = 1 / 2 := by field_simp
  refine ⟨η, hηpos, C7 * 14 ^ 7, by positivity, ?_⟩
  intro t ht σ hσ
  have hL := log_abs_gt_one ht
  have hL0 : 0 < Real.log |t| := by linarith
  have ht1 : 1 ≤ |t| := by linarith
  have ht0 : 0 < |t| := by linarith
  have hsqrt : |t| ^ ((1 : ℝ) / 2) * |t| ^ ((1 : ℝ) / 2) = |t| := by
    rw [← Real.rpow_add ht0]; norm_num
  have hhalf : 1 ≤ |t| ^ ((1 : ℝ) / 2) := Real.one_le_rpow ht1 (by norm_num)
  -- nonvanishing on the whole range
  have hnz : ∀ u ∈ Icc (1 - η / Real.log |t|) 2, ζ (u + t * I) ≠ 0 := by
    intro u hu
    by_cases hu1 : 1 ≤ u
    · apply riemannZeta_ne_zero_of_one_le_re; simpa using hu1
    · push Not at hu1
      apply hfree u t ht
      refine ⟨?_, hu1⟩
      rw [Real.rpow_one]
      have : η / Real.log |t| ≤ A₁ / Real.log |t| := by gcongr
      linarith [hu.1]
  refine ⟨hnz σ hσ, ?_⟩
  have hL7 := log_pow_seven_le ht1
  by_cases hσ1 : 1 ≤ σ
  · calc 1 / ‖ζ (σ + t * I)‖ ≤ C7 * Real.log |t| ^ (7 : ℝ) := h7 σ ⟨hσ1, hσ.2⟩ t ht
      _ ≤ C7 * (14 ^ 7 * |t| ^ ((1 : ℝ) / 2)) := by gcongr
      _ ≤ C7 * (14 ^ 7 * |t| ^ ((1 : ℝ) / 2)) * |t| ^ ((1 : ℝ) / 2) :=
          le_mul_of_one_le_right (by positivity) hhalf
      _ = C7 * 14 ^ 7 * |t| := by linear_combination (C7 * 14 ^ 7) * hsqrt
  · push Not at hσ1
    set K := Cd * Real.log |t| ^ (2 : ℝ) with hK
    have htne : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
    have hmv := norm_zeta_one_le (t := t) (σ := σ) (K := K) hσ1.le
      (fun u hu ↦ ⟨hnz u ⟨hσ.1.trans hu.1, by linarith [hu.2]⟩, by
        intro h; apply htne; have := congrArg Complex.im h; simpa using this⟩)
      (fun u hu ↦ hd u t ht (by
        show 1 - F / Real.log |t| ≤ u
        have : η / Real.log |t| ≤ F / Real.log |t| := by gcongr
        linarith [hσ.1, hu.1]))
    have hz1 : ζ (1 + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
    have hzσ := hnz σ hσ
    have hpos1 : 0 < ‖ζ (1 + t * I)‖ := norm_pos_iff.mpr hz1
    have hposσ : 0 < ‖ζ (σ + t * I)‖ := norm_pos_iff.mpr hzσ
    have hinv1 := h7 1 ⟨le_rfl, by norm_num⟩ t ht
    push_cast at hinv1
    -- exponent bound
    have hexp : Real.exp (K * (1 - σ)) ≤ |t| ^ ((1 : ℝ) / 2) := by
      have h1σ : 1 - σ ≤ η / Real.log |t| := by linarith [hσ.1]
      have : K * (1 - σ) ≤ (1 / 2) * Real.log |t| := by
        calc K * (1 - σ) ≤ K * (η / Real.log |t|) := by
              apply mul_le_mul_of_nonneg_left h1σ; positivity
          _ = (Cd * η) * Real.log |t| := by
              rw [hK, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
              field_simp
          _ ≤ (1 / 2) * Real.log |t| := by gcongr
      calc Real.exp (K * (1 - σ)) ≤ Real.exp ((1 / 2) * Real.log |t|) := Real.exp_le_exp.mpr this
        _ = |t| ^ ((1 : ℝ) / 2) := by
            rw [Real.rpow_def_of_pos ht0, mul_comm]
    calc 1 / ‖ζ (σ + t * I)‖ ≤ Real.exp (K * (1 - σ)) / ‖ζ (1 + t * I)‖ := by
          rw [div_le_div_iff₀ hposσ hpos1]; linarith
      _ = Real.exp (K * (1 - σ)) * (1 / ‖ζ (1 + t * I)‖) := by ring
      _ ≤ |t| ^ ((1 : ℝ) / 2) * (C7 * (14 ^ 7 * |t| ^ ((1 : ℝ) / 2))) := by
          gcongr
          exact hinv1.trans (by gcongr)
      _ = C7 * 14 ^ 7 * |t| := by linear_combination (C7 * 14 ^ 7) * hsqrt

/-- `1/ζ`, extended by `0` at the pole `s = 1`. -/
noncomputable def invZeta (s : ℂ) : ℂ := if s = 1 then 0 else (ζ s)⁻¹

lemma invZeta_of_ne {s : ℂ} (hs : s ≠ 1) : invZeta s = (ζ s)⁻¹ := by simp [invZeta, hs]

lemma invZeta_differentiableAt_of_ne {z : ℂ} (hz1 : z ≠ 1) (hz : ζ z ≠ 0) :
    DifferentiableAt ℂ invZeta z := by
  have heq : (fun s ↦ (ζ s)⁻¹) =ᶠ[𝓝 z] invZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show z ∈ ({1}ᶜ : Set ℂ) from hz1)] with s hs
    exact (invZeta_of_ne hs).symm
  exact ((differentiableAt_riemannZeta hz1).inv hz).congr_of_eventuallyEq heq.symm

lemma invZeta_tendsto_one : Tendsto invZeta (𝓝[≠] 1) (𝓝 0) := by
  have h1 : Tendsto (fun s : ℂ ↦ s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have : Tendsto (fun s : ℂ ↦ s - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 := h1.mul (riemannZeta_residue_one.inv₀ one_ne_zero)
  rw [zero_mul] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [invZeta_of_ne hs, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs', one_mul]

lemma invZeta_differentiableAt_one : DifferentiableAt ℂ invZeta 1 := by
  have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * ζ s ≠ 0 :=
    riemannZeta_residue_one.eventually_ne one_ne_zero
  obtain ⟨U, hU, hUP⟩ := mem_nhdsWithin.mp hev |> fun ⟨u, hu, h1u, hsub⟩ ↦
    (⟨u, hu.mem_nhds h1u, fun s hs hs1 ↦ hsub ⟨hs, hs1⟩⟩ :
      ∃ U ∈ 𝓝 (1 : ℂ), ∀ s ∈ U, s ∈ ({1}ᶜ : Set ℂ) → (s - 1) * ζ s ≠ 0)
  have hd : DifferentiableOn ℂ invZeta (U \ {1}) := by
    intro z hz
    have hz1 : z ≠ 1 := hz.2
    have := hUP z hz.1 hz1
    exact (invZeta_differentiableAt_of_ne hz1 (right_ne_zero_of_mul this)).differentiableWithinAt
  have hc : ContinuousAt invZeta 1 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    simpa [invZeta] using invZeta_tendsto_one
  exact ((differentiableOn_compl_singleton_and_continuousAt_iff hU).mp ⟨hd, hc⟩).differentiableAt hU

lemma invZeta_differentiableAt {z : ℂ} (hz : ζ z ≠ 0) : DifferentiableAt ℂ invZeta z := by
  by_cases h : z = 1
  · subst h; exact invZeta_differentiableAt_one
  · exact invZeta_differentiableAt_of_ne h hz

/-- Box near the real axis: zero-free and `invZeta` bounded. -/
lemma invZeta_box :
    ∃ σb : ℝ, σb < 1 ∧ 1 / 2 ≤ σb ∧ ∃ Bb > 0, ∀ σ ∈ Icc σb (2 : ℝ), ∀ t : ℝ, |t| ≤ 3 →
      ζ (σ + t * I) ≠ 0 ∧ ‖invZeta (σ + t * I)‖ ≤ Bb := by
  obtain ⟨σ₁, hσ₁, hbox⟩ := ZetaNoZerosInBox 3
  set σb := max σ₁ (1 / 2) with hσb
  have hσb1 : σb < 1 := max_lt hσ₁ (by norm_num)
  have hnz : ∀ σ ∈ Icc σb 2, ∀ t : ℝ, |t| ≤ 3 → ζ (σ + t * I) ≠ 0 :=
    fun σ hσ t ht ↦ hbox t ht σ ((le_max_left _ _).trans hσ.1)
  set K : Set ℂ := Icc σb 2 ×ℂ Icc (-3) 3 with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn invZeta K := by
    intro z hz
    have hz' : ζ z ≠ 0 := by
      have h := hnz z.re hz.1 z.im (abs_le.mpr ⟨hz.2.1, hz.2.2⟩)
      rwa [re_add_im] at h
    exact (invZeta_differentiableAt hz').continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨σb, hσb1, le_max_right _ _, max B 1, by positivity, fun σ hσ t ht ↦ ⟨hnz σ hσ t ht, ?_⟩⟩
  have hmem : (σ : ℂ) + t * I ∈ K := by
    refine ⟨?_, ?_⟩
    · simpa using hσ
    · simpa using abs_le.mp ht
  exact (hB _ hmem).trans (le_max_left _ _)

/-- **Region bound used for the contour shift.** -/
theorem invZeta_rect :
    ∃ η > 0, ∃ B > 0, ∃ T₀ ≥ 4, ∀ T ≥ T₀, 1 / 2 ≤ 1 - η / Real.log T ∧
      ∀ σ ∈ Icc (1 - η / Real.log T) 2, ∀ t : ℝ, |t| ≤ T →
        ζ (σ + t * I) ≠ 0 ∧ ‖invZeta (σ + t * I)‖ ≤ B * T := by
  obtain ⟨η, hη, C, hC, hstrip⟩ := inv_norm_zeta_le_strip
  obtain ⟨σb, hσb1, hσbh, Bb, hBb, hbox⟩ := invZeta_box
  refine ⟨η, hη, max C Bb, lt_max_of_lt_left hC, max 4 (Real.exp (η / (1 - σb))),
    le_max_left _ _, ?_⟩
  intro T hT
  have hT4 : 4 ≤ T := (le_max_left _ _).trans hT
  have hTe : Real.exp (η / (1 - σb)) ≤ T := (le_max_right _ _).trans hT
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlog : η / (1 - σb) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hTe
  have hσ0 : σb ≤ 1 - η / Real.log T := by
    have h1 : 0 < 1 - σb := by linarith
    have : η / Real.log T ≤ 1 - σb := by
      rw [div_le_iff₀ hlogT]
      rw [div_le_iff₀ h1] at hlog
      linarith
    linarith
  refine ⟨hσbh.trans hσ0, ?_⟩
  intro σ hσ t ht
  by_cases ht3 : |t| ≤ 3
  · obtain ⟨h1, h2⟩ := hbox σ ⟨hσ0.trans hσ.1, hσ.2⟩ t ht3
    refine ⟨h1, h2.trans ?_⟩
    calc Bb ≤ max C Bb := le_max_right _ _
      _ ≤ max C Bb * T := le_mul_of_one_le_right (by positivity) (by linarith)
  · push Not at ht3
    have hlt : Real.log |t| ≤ Real.log T := Real.log_le_log (by linarith) ht
    have hLt : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hσ' : σ ∈ Icc (1 - η / Real.log |t|) 2 := by
      refine ⟨?_, hσ.2⟩
      have : η / Real.log |t| ≥ η / Real.log T := div_le_div_of_nonneg_left hη.le hLt hlt
      linarith [hσ.1]
    obtain ⟨h1, h2⟩ := hstrip t ht3 σ hσ'
    refine ⟨h1, ?_⟩
    have hne : (σ : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; rw [this] at ht3; norm_num at ht3
    rw [invZeta_of_ne hne, norm_inv, ← one_div]
    calc 1 / ‖ζ (σ + t * I)‖ ≤ C * |t| := h2
      _ ≤ max C Bb * T := by gcongr; exact le_max_left _ _

end KerrPNT.Mobius
