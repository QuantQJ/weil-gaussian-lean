import Mathlib
import Reduction

/-!
# `ζ` commutes with complex conjugation; the nontrivial zeros are conjugation-closed

**Proven (unconditionally, no hypotheses, no axioms beyond Mathlib's standard three):**

* `hasDerivAt_conj_comp_conj` — if `f` has derivative `f'` at `conj s`, then
  `z ↦ conj (f (conj z))` has derivative `conj f'` at `s`. (Conjugation is only
  ℝ-linear, so this is done by hand from the little-o definition of `HasDerivAt`,
  using that `conj` is an isometry.)
* `riemannZeta_conj_of_one_lt_re` — `ζ (conj s) = conj (ζ s)` for `Re s > 1`, from the
  Dirichlet series and `Complex.cpow_conj`.
* `Gammaℝ_conj` — the Deligne factor `Γ_ℝ` commutes with `conj`.
* `completedRiemannZeta₀_conj` — the entire function `Λ₀` commutes with `conj`
  (identity theorem on `ℂ`, agreement on `Re s > 1`).
* `completedRiemannZeta_conj` — so does `Λ = Λ₀ - 1/s - 1/(1-s)`.
* `riemannZeta_conj` — **`ζ (conj s) = conj (ζ s)` for every `s : ℂ`**, including
  `s = 0` (`ζ 0 = -1/2`) and `s = 1` (Mathlib's convention `1/(1-1) = 0` is conj-stable).
* `isNontrivialZero_conj` — `Reduction.IsNontrivialZero ρ → Reduction.IsNontrivialZero (conj ρ)`.

Nothing is assumed; nothing is left unproven. No `sorry`, no axioms.
-/

noncomputable section
open Complex Filter Topology Set Asymptotics
open scoped ComplexConjugate

namespace ZetaConj

/-! ## Conjugating a holomorphic function -/

/-- If `f` has complex derivative `f'` at `conj s`, then `z ↦ conj (f (conj z))` has complex
derivative `conj f'` at `s`. Proven from the little-o characterisation of `HasDerivAt`,
since `conj` is a norm-preserving (ℝ-linear, not ℂ-linear) involution. -/
theorem hasDerivAt_conj_comp_conj {f : ℂ → ℂ} {s f' : ℂ} (hf : HasDerivAt f f' (conj s)) :
    HasDerivAt (fun z => conj (f (conj z))) (conj f') s := by
  rw [hasDerivAt_iff_isLittleO] at hf ⊢
  have h2 := hf.comp_tendsto (continuous_conj.tendsto s)
  rw [← isLittleO_norm_left, ← isLittleO_norm_right] at h2 ⊢
  refine h2.congr ?_ ?_
  · intro z
    simp only [Function.comp, smul_eq_mul]
    have : conj (f (conj z)) - conj (f (conj s)) - (z - s) * conj f'
        = conj (f (conj z) - f (conj s) - (conj z - conj s) * f') := by
      simp only [map_sub, map_mul, Complex.conj_conj]
    rw [this, Complex.norm_conj]
  · intro z
    simp only [Function.comp]
    rw [← map_sub, Complex.norm_conj]

/-- The conjugate-composed function of an entire function is entire. -/
theorem differentiable_conj_comp_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z => conj (f (conj z))) :=
  fun s => (hasDerivAt_conj_comp_conj (hf (conj s)).hasDerivAt).differentiableAt

/-! ## Agreement on the half-plane `Re s > 1` -/

/-- For a natural number `n`, `n ^ conj s = conj (n ^ s)`. -/
theorem natCast_cpow_conj (n : ℕ) (s : ℂ) : (n : ℂ) ^ (conj s) = conj ((n : ℂ) ^ s) := by
  rw [Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm),
    Complex.conj_natCast]

/-- `ζ (conj s) = conj (ζ s)` for `Re s > 1`, from the Dirichlet series. -/
theorem riemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have hs' : 1 < (conj s).re := by rwa [Complex.conj_re]
  rw [zeta_eq_tsum_one_div_nat_cpow hs, zeta_eq_tsum_one_div_nat_cpow hs', Complex.conj_tsum]
  congr 1
  funext n
  rw [map_div₀, map_one, natCast_cpow_conj]

/-- The Deligne factor `Γ_ℝ (s) = π ^ (-s/2) Γ(s/2)` commutes with conjugation. -/
theorem Gammaℝ_conj (s : ℂ) : Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul, ← Complex.Gamma_conj, map_div₀,
    Complex.conj_ofNat]
  congr 1
  · have hπ : ((Real.pi : ℂ)).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm
    have : -conj s / 2 = conj (-s / 2) := by
      rw [map_div₀, map_neg, Complex.conj_ofNat]
    rw [this, Complex.cpow_conj _ _ hπ, Complex.conj_ofReal]

/-- On `Re s > 1`, the entire function `Λ₀` commutes with conjugation. -/
theorem completedRiemannZeta₀_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; exact absurd hs (by norm_num)
  have hs0' : conj s ≠ 0 := by
    intro h; apply hs0; simpa using congrArg conj h
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΓ' : Complex.Gammaℝ (conj s) ≠ 0 := by rw [Gammaℝ_conj]; simpa using hΓ
  -- `Λ₀ s = ζ s * Γ_ℝ s + 1/s + 1/(1-s)` for `s ≠ 0` with `Γ_ℝ s ≠ 0`
  have key : ∀ t : ℂ, t ≠ 0 → Complex.Gammaℝ t ≠ 0 →
      completedRiemannZeta₀ t = riemannZeta t * Complex.Gammaℝ t + 1 / t + 1 / (1 - t) := by
    intro t ht hΓt
    rw [riemannZeta_def_of_ne_zero ht, div_mul_cancel₀ _ hΓt, completedRiemannZeta_eq]
    ring
  rw [key s hs0 hΓ, key (conj s) hs0' hΓ', riemannZeta_conj_of_one_lt_re hs, Gammaℝ_conj]
  simp only [map_add, map_mul, map_div₀, map_one, map_sub]

/-! ## Identity theorem on `ℂ` -/

/-- The entire function `Λ₀ = completedRiemannZeta₀` commutes with conjugation everywhere. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  set G : ℂ → ℂ := fun z => conj (completedRiemannZeta₀ (conj z)) with hG
  have hGan : AnalyticOnNhd ℂ G univ :=
    analyticOnNhd_univ_iff_differentiable.mpr
      (differentiable_conj_comp_conj differentiable_completedZeta₀)
  have hΛan : AnalyticOnNhd ℂ completedRiemannZeta₀ univ :=
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_completedZeta₀
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by simp
  have hfg : G =ᶠ[𝓝 (2 : ℂ)] completedRiemannZeta₀ := by
    filter_upwards [hopen.mem_nhds h2] with z hz
    simp only [hG]
    rw [completedRiemannZeta₀_conj_of_one_lt_re hz, Complex.conj_conj]
  have hEq := hGan.eqOn_of_preconnected_of_eventuallyEq hΛan isPreconnected_univ (mem_univ 2) hfg
  have := hEq (mem_univ s)
  simp only [hG] at this
  rw [← this, Complex.conj_conj]

/-- The completed zeta function `Λ = Λ₀ - 1/s - 1/(1-s)` commutes with conjugation. -/
theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq, completedRiemannZeta₀_conj]
  simp only [map_sub, map_div₀, map_one]

/-! ## Main results -/

/-- **`ζ` commutes with complex conjugation**, for every `s : ℂ`. -/
theorem riemannZeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) := by
  by_cases hs : s = 0
  · subst hs
    rw [map_zero, riemannZeta_zero]
    simp only [map_div₀, map_neg, map_one, Complex.conj_ofNat]
  · have hs' : conj s ≠ 0 := by
      intro h; apply hs; simpa using congrArg conj h
    rw [riemannZeta_def_of_ne_zero hs, riemannZeta_def_of_ne_zero hs', completedRiemannZeta_conj,
      Gammaℝ_conj, map_div₀]

/-- **The nontrivial zeros of `ζ` are closed under conjugation.** -/
theorem isNontrivialZero_conj {ρ : ℂ} (h : Reduction.IsNontrivialZero ρ) :
    Reduction.IsNontrivialZero (conj ρ) := by
  obtain ⟨h0, htriv, h1⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_conj, h0, map_zero]
  · rintro ⟨n, hn⟩
    apply htriv
    refine ⟨n, ?_⟩
    have := congrArg conj hn
    rw [Complex.conj_conj] at this
    rw [this]
    simp only [map_mul, map_neg, map_add, map_one, Complex.conj_natCast, Complex.conj_ofNat]
  · intro h
    apply h1
    have := congrArg conj h
    rwa [Complex.conj_conj, map_one] at this

end ZetaConj

end
