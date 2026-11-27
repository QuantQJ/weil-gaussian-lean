import OffLineDetection
import GaussianTraceFormula

/-!
# RH from a growth bound on the Gaussian zero trace

`OffLineDetection.RH_of_gaussian_trace` needs a tempered real sequence whose Gaussian traces equal
the zeros' traces. The proof only uses that equality to bound the zero trace by `√(π/b)·C'`.
This file takes that bound itself as the hypothesis:

  `RH_of_zero_trace_bound` : if for every centre `α` the zero trace
  `∑ₓ gaussHat b α (ordinate ρₓ)` is `O(b^{-1/2})` as `b → 0` (uniformly for `0 < b ≤ 1`), then RH.

`RH_iff_zero_trace_bound` adds the converse (under RH the zeros themselves are a tempered real
sequence, `OffLineDetection.real_side_bound`). The bound says nothing about how it is obtained:
a positive measure, a weighted stage limit, or heat positivity of the prime side can each supply it.
The proofs below are `OffLineDetection.key_estimate` / `ordinates_real` with the real side removed.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set
open scoped Real
open OffLineDetection Reduction ZeroSumLimit GaussianTest

namespace FleetTraceBoundRH

theorem key_estimate_of_bound
    (hS : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      Summable (fun x : Index => gaussHat b α (ordinate (canonical x))))
    (α : ℝ) (S : Finset Index) (hSsub : S ⊆ Zfin α) (M ε C C' b₀ : ℝ) (K : ℕ) (hb₀ : 0 < b₀)
    (hSM : ∀ x ∈ S, vE α (t x) = M)
    (hgap : ∀ x ∈ Zfin α, x ∉ S → vE α (t x) ≤ M - ε)
    (hC : ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, (Z α)ᶜ.indicator (fun x => gaussHat b α (t x)) x‖
        ≤ Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * C)
    (hZ : ∀ b : ℝ, 0 < b → b ≤ 1 →
      b < b₀ →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖ ≤ Real.sqrt (π / b) * (C' / b ^ K))
    (s : ℝ) (hs : 1 / 4 ≤ s) (hsb₀ : 1 / (4 * b₀) < s) :
    Real.exp (M * s) * ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖
      ≤ C' * (4 * s) ^ K + (Zfin α).card * Real.exp ((M - ε) * s)
        + C * Real.exp (-(3 / 4) * s) := by
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
  have hbb₀ : b < b₀ := by
    rw [hb_def, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hsb₀
    linarith
  have hreal := hZ b hb hb1 hbb₀
  change ‖∑' x, f x‖ ≤ Real.sqrt (π / b) * (C' / b ^ K) at hreal
  have hbK : C' / b ^ K = C' * (4 * s) ^ K := by
    rw [hb_def, one_div, inv_pow, div_eq_mul_inv, inv_inv]
  rw [hbK] at hreal
  -- assemble: `‖S-part‖ ≤ ‖total‖ + ‖mid‖ + ‖tail‖`
  have hkey : ‖∑ x ∈ S, f x‖ ≤ Real.sqrt (π / b) * (C' * (4 * s) ^ K)
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
      ≤ Real.sqrt (π / b) * (C' * (4 * s) ^ K + (Zfin α).card * Real.exp ((M - ε) * s)
        + C * Real.exp (-(3 / 4) * s)) := by
    convert hkey using 1 <;> ring
  exact le_of_mul_le_mul_left hkey' hsqrt

/-- `s ↦ C' (4s)^K e^{-Ms} + N e^{-εs} + C e^{-(M+3/4)s} → 0`: a polynomial prefactor on the
leading term changes nothing, because `exp` beats any power. -/
lemma tendsto_poly_bound (C' : ℝ) (K : ℕ) (N C M ε : ℝ) (hM : 0 < M) (hε : 0 < ε) :
    Tendsto (fun s : ℝ => C' * (4 * s) ^ K * Real.exp (-(M * s)) + N * Real.exp (-(ε * s))
      + C * Real.exp (-((M + 3 / 4) * s))) atTop (𝓝 0) := by
  have hM0 : M ≠ 0 := ne_of_gt hM
  have hcomp : Tendsto (fun s : ℝ => (M * s) ^ K * Real.exp (-(M * s))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K).comp (tendsto_id.const_mul_atTop hM)
  have h1 : Tendsto (fun s : ℝ => (4 * s) ^ K * Real.exp (-(M * s))) atTop (𝓝 0) := by
    have hc : Tendsto (fun s : ℝ => (4 / M) ^ K * ((M * s) ^ K * Real.exp (-(M * s))))
        atTop (𝓝 0) := by simpa using hcomp.const_mul ((4 / M) ^ K)
    refine hc.congr (fun s => ?_)
    rw [← mul_assoc, ← mul_pow]
    congr 2
    field_simp
  have h2 : Tendsto (fun s : ℝ => Real.exp (-(ε * s))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hε)
  have h3 : Tendsto (fun s : ℝ => Real.exp (-((M + 3 / 4) * s))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by linarith))
  have := ((h1.const_mul C').add (h2.const_mul N)).add (h3.const_mul C)
  simpa [mul_assoc] using this

theorem ordinates_real_of_bound (K : ℕ)
    (hS : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      Summable (fun x : Index => gaussHat b α (ordinate (canonical x))))
    (hZ : ∀ α : ℝ, ∃ C' b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ 1 → b < b₀ →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖
        ≤ Real.sqrt (π / b) * (C' / b ^ K)) :
    ∀ x : Index, (ordinate (canonical x)).im = 0 := by
  classical
  intro x₀
  by_contra hβ
  change (t x₀).im ≠ 0 at hβ
  set α : ℝ := (t x₀).re with hα
  -- `x₀` lies in the near set
  have hx₀ : x₀ ∈ Zfin α := by
    rw [mem_Zfin, hα, sub_self, abs_zero]
    exact one_pos
  have hne : (Zfin α).Nonempty := ⟨x₀, hx₀⟩
  -- the maximal value `M` of `v` on the near set
  obtain ⟨xm, hxm, hmax⟩ := Finset.exists_max_image (Zfin α) (fun x => vE α (t x)) hne
  set M : ℝ := vE α (t xm) with hM_def
  have hMpos : 0 < M := by
    have h0 : vE α (t x₀) = (t x₀).im ^ 2 := by
      simp only [vE, hα, sub_self]
      ring
    have h1 : 0 < (t x₀).im ^ 2 := by positivity
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
  obtain ⟨C, -, hC⟩ := tail_bound α
  obtain ⟨C', b₀, hb₀, hC'⟩ := hZ α
  -- the quantitative estimate, in the form `‖E s‖ ≤ B s`
  have hEst : ∀ s : ℝ, 1 / 4 ≤ s → 1 / (4 * b₀) < s →
      ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖
        ≤ C' * (4 * s) ^ K * Real.exp (-(M * s)) + (Zfin α).card * Real.exp (-(ε * s))
          + C * Real.exp (-((M + 3 / 4) * s)) := by
    intro s hs hsb₀
    have h := key_estimate_of_bound hS α S hSsub M ε C C' b₀ K hb₀ hSM hgap' hC hC' s hs hsb₀
    have hexp : 0 < Real.exp (M * s) := Real.exp_pos _
    refine le_of_mul_le_mul_right ?_ hexp
    have e1 : Real.exp (-(M * s)) * Real.exp (M * s) = 1 := by
      rw [← Real.exp_add]; simp
    have e2 : Real.exp (-(ε * s)) * Real.exp (M * s) = Real.exp ((M - ε) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    have e3 : Real.exp (-((M + 3 / 4) * s)) * Real.exp (M * s) = Real.exp (-(3 / 4) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖ * Real.exp (M * s)
        = Real.exp (M * s) * ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖ := by
          ring
      _ ≤ C' * (4 * s) ^ K + (Zfin α).card * Real.exp ((M - ε) * s)
          + C * Real.exp (-(3 / 4) * s) := h
      _ = (C' * (4 * s) ^ K * Real.exp (-(M * s)) + (Zfin α).card * Real.exp (-(ε * s))
          + C * Real.exp (-((M + 3 / 4) * s))) * Real.exp (M * s) := by
          linear_combination (-(C' * (4 * s) ^ K)) * e1 - ((Zfin α).card : ℝ) * e2 - C * e3
  -- the bound tends to `0`, so it is `< 1/2` for large `s`
  have hB := tendsto_poly_bound C' K (Zfin α).card C M ε hMpos hε
  obtain ⟨S₁, hS₁⟩ := Filter.eventually_atTop.mp (hB.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2))
  -- but `‖E s‖ ≥ 1/2` at arbitrarily large `s`
  obtain ⟨s, hs, hlarge⟩ :=
    ExpSumLowerBound.exists_large_of_nonempty S hSne (fun x => thetaE α (t x))
      (max (max S₁ (1 / 4)) (1 / (4 * b₀) + 1))
  have hs1 : S₁ ≤ s :=
    le_trans (le_trans (le_max_left S₁ (1 / 4)) (le_max_left _ _)) hs
  have hs2 : 1 / 4 ≤ s :=
    le_trans (le_trans (le_max_right S₁ (1 / 4)) (le_max_left _ _)) hs
  have hs3 : 1 / (4 * b₀) < s := by
    have := le_trans (le_max_right (max S₁ (1 / 4)) (1 / (4 * b₀) + 1)) hs
    linarith
  have := hS₁ s hs1
  have := hEst s hs2 hs3
  linarith


/-- **RH from a growth bound with any polynomial normalisation.**  The hypothesis is
`O(b^{-1/2-K})` for a fixed `K : ℕ`, not the sharp `O(b^{-1/2})`.  The sharp exponent is not
what drives the argument: `√(π/b)` cancels identically between the two sides of the key
estimate, and the contradiction only needs the normalised trace to grow more slowly than
`exp(M/(4b))`, which every power of `1/b` does. -/
theorem RH_of_zero_trace_small_b_bound (K : ℕ)
    (hS : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      Summable (fun x : Index => gaussHat b α (ordinate (canonical x))))
    (hZ : ∀ α : ℝ, ∃ C' b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ 1 → b < b₀ →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖
        ≤ Real.sqrt (π / b) * (C' / b ^ K)) :
    RiemannHypothesis := by
  apply RH_of_nontrivial_zeros_on_critical_line
  intro ρ hρ
  obtain ⟨x, hx⟩ := multEnum_canonical.exists_index hρ
  have h := ordinates_real_of_bound K hS hZ x
  rw [hx, ordinate_im] at h
  linarith

theorem RH_of_zero_trace_poly_bound (K : ℕ)
    (hS : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      Summable (fun x : Index => gaussHat b α (ordinate (canonical x))))
    (hZ : ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖
        ≤ Real.sqrt (π / b) * (C' / b ^ K)) :
    RiemannHypothesis :=
  RH_of_zero_trace_small_b_bound K hS
    (fun α => by
      obtain ⟨C', hC'⟩ := hZ α
      exact ⟨C', 2, by norm_num, fun b hb hb1 _ => hC' b hb hb1⟩)

/-- **RH from the growth bound.** -/
theorem RH_of_zero_trace_bound
    (hS : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      Summable (fun x : Index => gaussHat b α (ordinate (canonical x))))
    (hZ : ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖ ≤ Real.sqrt (π / b) * C') :
    RiemannHypothesis := by
  refine RH_of_zero_trace_poly_bound 0 hS (fun α => ?_)
  obtain ⟨C', hC'⟩ := hZ α
  exact ⟨C', fun b hb hb1 => by simpa using hC' b hb hb1⟩

/-- **Converse.** Under RH the zero trace satisfies the growth bound: the zeros themselves are a
tempered real sequence. -/
theorem zero_trace_bound_of_RH (hRH : RiemannHypothesis) :
    ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖ ≤ Real.sqrt (π / b) * C' := by
  intro α
  have hreal : ∀ x : Index, ordinate (canonical x) = (((t x).re : ℝ) : ℂ) := by
    intro x
    have hre : (canonical x).re = 1 / 2 := riemannHypothesis_iff.mp hRH _ x.1.2
    have him : (t x).im = 0 := by rw [t_im, hre]; norm_num
    apply Complex.ext
    · simp [t]
    · simpa [t] using him
  obtain ⟨C', hC'⟩ := real_side_bound (fun x : Index => (t x).re) summable_inv_one_add_sq_re α
  refine ⟨C', fun b hb hb1 => ?_⟩
  have e : (fun x : Index => gaussHat b α (ordinate (canonical x)))
      = fun x => gaussHat b α ((((t x).re : ℝ)) : ℂ) := funext fun x => by rw [hreal x]
  rw [e]
  exact hC' b hb hb1

/-- **Equivalence.** RH holds iff every centre's Gaussian zero trace is `O(b^{-1/2})`. -/
theorem RH_iff_zero_trace_bound
    (hS : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      Summable (fun x : Index => gaussHat b α (ordinate (canonical x)))) :
    RiemannHypothesis ↔ ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖ ≤ Real.sqrt (π / b) * C' :=
  ⟨zero_trace_bound_of_RH, RH_of_zero_trace_bound hS⟩

/-- **Unconditional form.** Summability of the zero trace is discharged by
`GaussianTraceFormula.gaussian_formula_zeros`: RH holds iff, for every centre `α`, the Gaussian
zero trace is `O(b^{-1/2})` uniformly for `0 < b ≤ 1`. -/
theorem RH_iff_zero_trace_bound' :
    RiemannHypothesis ↔ ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖ ≤ Real.sqrt (π / b) * C' :=
  RH_iff_zero_trace_bound (fun _ hb α => (GaussianTraceFormula.gaussian_formula_zeros hb α).summable)

end FleetTraceBoundRH
