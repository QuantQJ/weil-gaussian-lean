import FleetPrimeTarget

/-!
# The exponent ladder: partial bounds give zero-free strips

`RH_iff_zero_trace_bound'` needs the Gaussian zero trace to be `O(b^{-1/2})`. Here the bound is relaxed to
`√(π/b) · C' · e^{c/b}`. The same off-line detection argument then gives, for every nontrivial zero,
`(Re ρ − 1/2)² ≤ 4c`, i.e. `|Re ρ − 1/2| ≤ 2√c` (`zeros_in_strip_of_exp_bound`). With `c = 0` this is RH; the trivial
prime-side bound corresponds to `c = 1/16` (the strip `0 < Re ρ < 1`). Any `c < 1/16` would be a zero-free vertical
strip. `zeros_in_strip_of_pole_prime_exp_bound` states the same with the prime-side functional `poleMinusPrimes`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set
open scoped Real
open OffLineDetection Reduction ZeroSumLimit GaussianTest

namespace FleetExponentLadder

theorem key_estimate_of_exp_bound
    (hS : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      Summable (fun x : Index => gaussHat b α (ordinate (canonical x))))
    (α : ℝ) (S : Finset Index) (hSsub : S ⊆ Zfin α) (M ε C C' : ℝ)
    (hSM : ∀ x ∈ S, vE α (t x) = M)
    (hgap : ∀ x ∈ Zfin α, x ∉ S → vE α (t x) ≤ M - ε)
    (hC : ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, (Z α)ᶜ.indicator (fun x => gaussHat b α (t x)) x‖
        ≤ Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * C)
    (c : ℝ)
    (hZ : ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖ ≤ Real.sqrt (π / b) * (C' * Real.exp (c / b)))
    (s : ℝ) (hs : 1 / 4 ≤ s) :
    Real.exp (M * s) * ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖
      ≤ C' * Real.exp (4 * c * s) + (Zfin α).card * Real.exp ((M - ε) * s) + C * Real.exp (-(3 / 4) * s) := by
  classical
  set b : ℝ := 1 / (4 * s) with hb_def
  have hs0 : 0 < s := by linarith
  have hb : 0 < b := by positivity
  have hb1 : b ≤ 1 := by
    rw [hb_def, div_le_one (by positivity)]
    linarith
  have hsb : s = 1 / (4 * b) := by
    rw [hb_def]
    field_simp
  have h316 : -3 / (16 * b) = -(3 / 4) * s := by
    rw [hb_def]
    field_simp
    ring
  have hsqrt : 0 < Real.sqrt (π / b) := Real.sqrt_pos.2 (div_pos Real.pi_pos hb)
  set f : Index → ℂ := fun x => gaussHat b α (t x) with hf_def
  have hfS : Summable f := hS b hb α
  -- the zero side, split three ways
  have hsplit := tsum_split α f hfS
  rw [← Finset.sum_filter_add_sum_filter_not (Zfin α) (fun x => x ∈ S)] at hsplit
  have hfilt : (Zfin α).filter (fun x => x ∈ S) = S := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hSsub h, h⟩⟩
  rw [hfilt] at hsplit
  -- the `S`-part is `√(π/b) exp(M s) · E s`
  have hSpart : ∑ x ∈ S, f x
      = ((Real.sqrt (π / b) * Real.exp (M * s) : ℝ) : ℂ)
        * ∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp only [hf_def]
    rw [gaussHat_polar hb α (t x) hsb, hSM x hx]
    push_cast
    ring
  -- the middle part
  have hmid : ‖∑ x ∈ (Zfin α).filter (fun x => x ∉ S), f x‖
      ≤ (Zfin α).card * (Real.sqrt (π / b) * Real.exp ((M - ε) * s)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (Real.sqrt (π / b) * Real.exp ((M - ε) * s))
      (fun x hx => ?_)).trans ?_
    · have hx' := Finset.mem_filter.mp hx
      simp only [hf_def]
      rw [norm_gaussHat_s hb α (t x) hsb]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right (hgap x hx'.1 hx'.2) hs0.le
    · rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast Finset.card_filter_le _ _
  -- the tail and the real side
  have htail := hC b hb hb1
  have hreal := hZ b hb hb1
  have hcb : c / b = 4 * c * s := by rw [hb_def]; field_simp
  rw [hcb] at hreal
  change ‖∑' x, f x‖ ≤ Real.sqrt (π / b) * (C' * Real.exp (4 * c * s)) at hreal
  -- assemble: `‖S-part‖ ≤ ‖total‖ + ‖mid‖ + ‖tail‖`
  have hkey : ‖∑ x ∈ S, f x‖ ≤ Real.sqrt (π / b) * (C' * Real.exp (4 * c * s))
      + (Zfin α).card * (Real.sqrt (π / b) * Real.exp ((M - ε) * s))
      + Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * C := by
    have : ∑ x ∈ S, f x = ∑' x, f x - ∑ x ∈ (Zfin α).filter (fun x => x ∉ S), f x
        - ∑' x, (Z α)ᶜ.indicator f x := by
      rw [hsplit]; ring
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add hreal hmid)) htail
  rw [hSpart, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    _root_.abs_of_nonneg (by positivity), h316] at hkey
  -- divide by `√(π/b)`
  have hkey' : Real.sqrt (π / b) * (Real.exp (M * s)
      * ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖)
      ≤ Real.sqrt (π / b) * (C' * Real.exp (4 * c * s) + (Zfin α).card * Real.exp ((M - ε) * s)
        + C * Real.exp (-(3 / 4) * s)) := by
    convert hkey using 1 <;> ring
  exact le_of_mul_le_mul_left hkey' hsqrt

theorem ordinate_im_sq_le_of_exp_bound
    (hS : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      Summable (fun x : Index => gaussHat b α (ordinate (canonical x))))
    {c : ℝ} (hc : 0 ≤ c)
    (hZ : ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖ ≤ Real.sqrt (π / b) * (C' * Real.exp (c / b))) :
    ∀ x : Index, (ordinate (canonical x)).im ^ 2 ≤ 4 * c := by
  classical
  intro x₀
  by_contra hβ
  push_neg at hβ
  change 4 * c < (t x₀).im ^ 2 at hβ
  set α : ℝ := (t x₀).re with hα
  -- `x₀` lies in the near set
  have hx₀ : x₀ ∈ Zfin α := by
    rw [mem_Zfin, hα, sub_self, abs_zero]
    exact one_pos
  have hne : (Zfin α).Nonempty := ⟨x₀, hx₀⟩
  -- the maximal value `M` of `v` on the near set
  obtain ⟨xm, hxm, hmax⟩ := Finset.exists_max_image (Zfin α) (fun x => vE α (t x)) hne
  set M : ℝ := vE α (t xm) with hM_def
  have hMpos : 0 < M - 4 * c := by
    have h0 : vE α (t x₀) = (t x₀).im ^ 2 := by
      simp only [vE, hα, sub_self]
      ring
    have := hmax x₀ hx₀
    linarith
  -- the set `S` where the maximum is attained, and the gap `ε`
  set S : Finset Index := (Zfin α).filter (fun x => vE α (t x) = M) with hS_def
  have hSsub : S ⊆ Zfin α := Finset.filter_subset _ _
  have hSne : S.Nonempty := ⟨xm, Finset.mem_filter.mpr ⟨hxm, rfl⟩⟩
  have hSM : ∀ x ∈ S, vE α (t x) = M := fun x hx => (Finset.mem_filter.mp hx).2
  obtain ⟨ε, hε, hgap⟩ := exists_gap (Zfin α) (fun x => vE α (t x)) M (fun x hx => hmax x hx)
  have hgap' : ∀ x ∈ Zfin α, x ∉ S → vE α (t x) ≤ M - ε := by
    intro x hx hxS
    refine hgap x hx (fun h => hxS (Finset.mem_filter.mpr ⟨hx, h⟩))
  -- constants
  obtain ⟨C, hC0, hC⟩ := tail_bound α
  obtain ⟨C', hC'⟩ := hZ α
  -- the quantitative estimate, in the form `‖E s‖ ≤ B s`
  have hEst : ∀ s : ℝ, 1 / 4 ≤ s →
      ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖
        ≤ C' * Real.exp (-((M - 4 * c) * s)) + (Zfin α).card * Real.exp (-(ε * s))
          + C * Real.exp (-((M - 4 * c + 3 / 4) * s)) := by
    intro s hs
    have h := key_estimate_of_exp_bound hS α S hSsub M ε C C' hSM hgap' hC c hC' s hs
    have hs0 : 0 ≤ s := by linarith
    have hthird : C * Real.exp (-((M + 3 / 4) * s)) ≤ C * Real.exp (-((M - 4 * c + 3 / 4) * s)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hC0
    refine le_trans ?_ (add_le_add_right hthird _)
    have hexp : 0 < Real.exp (M * s) := Real.exp_pos _
    refine le_of_mul_le_mul_right ?_ hexp
    have e1 : Real.exp (-((M - 4 * c) * s)) * Real.exp (M * s) = Real.exp (4 * c * s) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(ε * s)) * Real.exp (M * s) = Real.exp ((M - ε) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    have e3 : Real.exp (-((M + 3 / 4) * s)) * Real.exp (M * s) = Real.exp (-(3 / 4) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖ * Real.exp (M * s)
        = Real.exp (M * s) * ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖ := by
          ring
      _ ≤ C' * Real.exp (4 * c * s) + (Zfin α).card * Real.exp ((M - ε) * s) + C * Real.exp (-(3 / 4) * s) := h
      _ = (C' * Real.exp (-((M - 4 * c) * s)) + (Zfin α).card * Real.exp (-(ε * s))
          + C * Real.exp (-((M + 3 / 4) * s))) * Real.exp (M * s) := by
          linear_combination (-C') * e1 - ((Zfin α).card : ℝ) * e2 - C * e3
  -- the bound tends to `0`, so it is `< 1/2` for large `s`
  have hB := tendsto_bound C' (Zfin α).card C (M - 4 * c) ε hMpos hε
  obtain ⟨S₁, hS₁⟩ := Filter.eventually_atTop.mp (hB.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2))
  -- but `‖E s‖ ≥ 1/2` at arbitrarily large `s`
  obtain ⟨s, hs, hlarge⟩ :=
    ExpSumLowerBound.exists_large_of_nonempty S hSne (fun x => thetaE α (t x)) (max S₁ (1 / 4))
  have hs1 : S₁ ≤ s := le_trans (le_max_left _ _) hs
  have hs2 : 1 / 4 ≤ s := le_trans (le_max_right _ _) hs
  have := hS₁ s hs1
  have := hEst s hs2
  linarith

/-- **The ladder on the zero side**: an `e^{c/b}` allowance confines every zero to `|Re ρ − 1/2| ≤ 2√c`. -/
theorem zeros_in_strip_of_exp_bound {c : ℝ} (hc : 0 ≤ c)
    (hZ : ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖ ≤ Real.sqrt (π / b) * (C' * Real.exp (c / b))) :
    ∀ x : Index, |(canonical x).re - 1 / 2| ≤ 2 * Real.sqrt c := by
  intro x
  have h := ordinate_im_sq_le_of_exp_bound
    (fun _ hb α => (GaussianTraceFormula.gaussian_formula_zeros hb α).summable) hc hZ x
  rw [ordinate_im] at h
  have e : (canonical x).re - 1 / 2 = -(1 / 2 - (canonical x).re) := by ring
  rw [e, abs_neg]
  have h4 : Real.sqrt (4 * c) = 2 * Real.sqrt c := by
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  rw [← h4]
  exact Real.abs_le_sqrt h

/-- **The ladder on the prime side**: if `‖poleMinusPrimes b α‖ ≤ √(π/b) C' e^{c/b}` at every centre, every zero
satisfies `|Re ρ − 1/2| ≤ 2√c`. -/
theorem zeros_in_strip_of_pole_prime_exp_bound {c : ℝ} (hc : 0 ≤ c)
    (hP : ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖FleetPrimePoleBoundRH.poleMinusPrimes b α‖ ≤ Real.sqrt (π / b) * (C' * Real.exp (c / b))) :
    ∀ x : Index, |(canonical x).re - 1 / 2| ≤ 2 * Real.sqrt c := by
  obtain ⟨K, hK, hA⟩ := FleetPrimePoleBoundRH.norm_archimedean_le
  refine zeros_in_strip_of_exp_bound hc (fun α => ?_)
  obtain ⟨C', hC'⟩ := hP α
  refine ⟨C' + ‖(1 / (2 * (Real.pi : ℂ)))‖ * K * (9 + 2 * α ^ 2), fun b hb hb1 => ?_⟩
  have hE : 1 ≤ Real.exp (c / b) := Real.one_le_exp (div_nonneg hc hb.le)
  have hAk : 0 ≤ ‖(1 / (2 * (Real.pi : ℂ)))‖ * K * (9 + 2 * α ^ 2) := by positivity
  rw [FleetPrimePoleBoundRH.zero_trace_eq_rhs hb α, FleetPrimePoleBoundRH.rhs_split]
  refine (norm_add_le _ _).trans ?_
  have h2 : ‖FleetFullLineArithmetic.archimedean (gauss b α)‖
      ≤ Real.sqrt (π / b) * (‖(1 / (2 * (Real.pi : ℂ)))‖ * K * (9 + 2 * α ^ 2) * Real.exp (c / b)) :=
    (hA α b hb hb1).trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hAk hE) (Real.sqrt_nonneg _))
  calc _ ≤ Real.sqrt (π / b) * (C' * Real.exp (c / b))
        + Real.sqrt (π / b) * (‖(1 / (2 * (Real.pi : ℂ)))‖ * K * (9 + 2 * α ^ 2) * Real.exp (c / b)) :=
        add_le_add (hC' b hb hb1) h2
    _ = _ := by ring

end FleetExponentLadder
