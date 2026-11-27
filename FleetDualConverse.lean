import FleetRationalBanks
import Mathlib

/-!
# The converse: the prime-side inequality implies stage feasibility (weighted atoms)

Fix a stage `n`, write `S` for the bank centres and `R q` for the real arithmetic target.
A *weighted* stage solution is a finitely supported nonnegative weight `a` on real points with

  `Σ_x a x · (1+x²)⁻¹ ≤ M`   and   `|Σ_x a x · √π e^{-(x-q)²/4} − R q| ≤ ε`   for every `q ∈ S`.

`DualIneq M ε n` is the prime-side inequality for every weighting `c` of the centres:
whenever `-φ_c ≤ K · (1+t²)⁻¹` with `K ≥ 0`, `-(K·M) - ε·Σ|c| ≤ Σ c q · R q`.

Main results (all standard axioms):
* `weightedFeasible_of_dualIneq` : `0 < M`, `0 ≤ ε`, `DualIneq M ε n`, `0 < δ` ⇒ weighted solution at tolerance `ε + δ`.
  Proof: Hahn–Banach separation of the compact tolerance box from the closure of the
  (convex) set of achievable trace vectors; a separating functional is a weighting `c`
  whose existence contradicts the inequality.
* `dualIneq_of_weightedFeasible` : the forward direction for weighted solutions.
* `weightedFeasible_iff_dualIneq` : for `0 < M`, `0 ≤ ε`, (∀ δ > 0, weighted solution at `ε + δ`) ↔ `DualIneq M ε n`.

Weighted atoms are real points with nonnegative real weights. `FleetRationalBankCriterion.Feasible`
uses unit weights; the inequality cannot force integer weights by itself (a half-weight atom
satisfies every such inequality), so this file is the exact converse for the weighted problem.
-/

noncomputable section
open Filter

namespace FleetDualConverse

/-- Bank centres of stage `n` as a finite type. -/
abbrev S (n : ℕ) := {q : ℚ // q ∈ FleetRationalBanks.bank n}

/-- Width-one probe. -/
def G (x : ℝ) (q : ℚ) : ℝ := Real.sqrt Real.pi * Real.exp (-(x - (q : ℝ))^2/4)

/-- Mass weight. -/
def w (x : ℝ) : ℝ := (1 + x^2)⁻¹

lemma w_pos (x : ℝ) : 0 < w x := by unfold w; positivity

/-- Gaussian combination with weights on the bank. -/
def phi {n : ℕ} (c : S n → ℝ) (t : ℝ) : ℝ := ∑ q : S n, c q * G t q

/-- Trace vector of a weight, as a linear map. -/
def traceMap (n : ℕ) : (ℝ →₀ ℝ) →ₗ[ℝ] (S n → ℝ) :=
  Finsupp.linearCombination ℝ (fun x : ℝ => fun q : S n => G x q)

/-- Mass of a weight, as a linear map. -/
def massMap : (ℝ →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.linearCombination ℝ w

/-- Weighted stage solution at budget `M`, tolerance `ε`. -/
def WeightedFeasible (R : ℚ → ℝ) (M ε : ℝ) (n : ℕ) : Prop :=
  ∃ a : ℝ →₀ ℝ, (∀ x, 0 ≤ a x) ∧ massMap a ≤ M ∧ ∀ q : S n, |traceMap n a q - R q| ≤ ε

/-- The prime-side inequality at stage `n`. -/
def DualIneq (R : ℚ → ℝ) (M ε : ℝ) (n : ℕ) : Prop :=
  ∀ (c : S n → ℝ) (K : ℝ), 0 ≤ K → (∀ t : ℝ, -phi c t ≤ K * w t) →
    -(K * M) - ε * ∑ q : S n, |c q| ≤ ∑ q : S n, c q * R q

/-- Achievable trace vectors within budget `M`. -/
def achievable (n : ℕ) (M : ℝ) : Set (S n → ℝ) :=
  traceMap n '' {a | (∀ x, 0 ≤ a x) ∧ massMap a ≤ M}

lemma convex_achievable (n : ℕ) (M : ℝ) : Convex ℝ (achievable n M) := by
  apply Convex.linear_image
  intro a ha b hb s t hs ht hst
  refine ⟨fun x => ?_, ?_⟩
  · simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := ha.1 x; have := hb.1 x; positivity
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left ha.2 hs
    have h2 := mul_le_mul_of_nonneg_left hb.2 ht
    calc s * massMap a + t * massMap b ≤ s * M + t * M := add_le_add h1 h2
      _ = M := by rw [← add_mul, hst, one_mul]

/-- Pairing of a weighting with a trace vector equals the weight sum of `phi`. -/
lemma pairing_trace {n : ℕ} (c : S n → ℝ) (a : ℝ →₀ ℝ) :
    ∑ q : S n, c q * traceMap n a q = a.sum (fun x r => r * phi c x) := by
  simp only [traceMap, Finsupp.linearCombination_apply, phi, Finsupp.sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun q _ => by ring))

lemma mass_eq (a : ℝ →₀ ℝ) : massMap a = a.sum (fun x r => r * w x) := by
  simp only [massMap, Finsupp.linearCombination_apply, smul_eq_mul]

/-- Forward direction for weighted solutions. -/
theorem dualIneq_of_weightedFeasible {R : ℚ → ℝ} {M ε : ℝ} {n : ℕ}
    (hf : WeightedFeasible R M ε n) : DualIneq R M ε n := by
  obtain ⟨a, ha0, hm, hr⟩ := hf
  intro c K hK hneg
  have hatoms : -(K * M) ≤ ∑ q : S n, c q * traceMap n a q := by
    rw [pairing_trace]
    have h1 : a.sum (fun x r => r * (-(K * w x))) ≤ a.sum (fun x r => r * phi c x) := by
      unfold Finsupp.sum
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (by linarith [hneg x]) (ha0 x)
    have h2 : a.sum (fun x r => r * (-(K * w x))) = -(K * massMap a) := by
      rw [mass_eq]; unfold Finsupp.sum
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    have h3 : K * massMap a ≤ K * M := mul_le_mul_of_nonneg_left hm hK
    linarith
  have hrep : ∑ q : S n, c q * traceMap n a q - ε * ∑ q : S n, |c q| ≤ ∑ q : S n, c q * R q := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro q _
    have key : |c q * (traceMap n a q - R q)| ≤ |c q| * ε := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hr q) (abs_nonneg _)
    have := (abs_le.mp key).2
    nlinarith
  linarith

/-- Converse: the prime-side inequality forces a weighted stage solution, at any tolerance
above `ε`. -/
theorem weightedFeasible_of_dualIneq {R : ℚ → ℝ} {M ε : ℝ} {n : ℕ} (hM : 0 < M) (hε : 0 ≤ ε)
    (hd : DualIneq R M ε n) {δ : ℝ} (hδ : 0 < δ) : WeightedFeasible R M (ε + δ) n := by
  classical
  let r : S n → ℝ := fun q => R q
  let B : Set (S n → ℝ) := Metric.closedBall r ε
  let T : Set (S n → ℝ) := closure (achievable n M)
  -- the box meets the closure of the achievable set
  have hmeet : (B ∩ T).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hdisj : Disjoint B T := Set.disjoint_iff_inter_eq_empty.mpr hne
    obtain ⟨f, u, v, hfB, huv, hfT⟩ := geometric_hahn_banach_compact_closed
      (convex_closedBall r ε) (isCompact_closedBall r ε)
      ((convex_achievable n M).closure) isClosed_closure hdisj
    let c : S n → ℝ := fun i => f (fun j => if i = j then 1 else 0)
    have hf : ∀ p : S n → ℝ, f p = ∑ q : S n, c q * p q := by
      intro p
      have := LinearMap.pi_apply_eq_sum_univ (f : (S n → ℝ) →ₗ[ℝ] ℝ) p
      simpa [c, smul_eq_mul, mul_comm] using this
    -- the corner of the box in the direction of c
    let p : S n → ℝ := fun q => r q + (if 0 ≤ c q then ε else -ε)
    have hpB : p ∈ B := by
      rw [Metric.mem_closedBall, dist_pi_le_iff hε]
      intro q
      rw [Real.dist_eq]
      simp only [p, add_sub_cancel_left]
      split_ifs <;> simp [abs_of_nonneg hε]
    have hpval : f p = ∑ q : S n, c q * R q + ε * ∑ q : S n, |c q| := by
      rw [hf, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp only [p, r]
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · push_neg at h; rw [abs_of_neg h]; ring
    have hu := hfB p hpB
    -- the zero weight is achievable: v < 0
    have h0T : (0 : S n → ℝ) ∈ T := subset_closure
      ⟨0, ⟨fun x => le_refl _, by simp [hM.le]⟩, by simp⟩
    have hv0 : v < 0 := by have := hfT 0 h0T; simpa using this
    -- a single atom carrying the full budget at x
    have hatom : ∀ x : ℝ, v < M * (1 + x^2) * phi c x := by
      intro x
      let s : ℝ := M * (1 + x^2)
      have hs : 0 ≤ s := by positivity
      have hmem : traceMap n (Finsupp.single x s) ∈ T := by
        refine subset_closure ⟨Finsupp.single x s, ⟨fun y => ?_, ?_⟩, rfl⟩
        · by_cases hy : x = y
          · subst hy; simp [hs]
          · simp [Finsupp.single_apply, hy]
        · simp only [massMap, Finsupp.linearCombination_single, smul_eq_mul, s, w]
          rw [mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
      have := hfT _ hmem
      rw [hf] at this
      have e : ∑ q : S n, c q * traceMap n (Finsupp.single x s) q = s * phi c x := by
        simp only [traceMap, Finsupp.linearCombination_single, Pi.smul_apply, smul_eq_mul, phi,
          Finset.mul_sum]
        exact Finset.sum_congr rfl (fun q _ => by ring)
      rw [e] at this
      exact this
    -- apply the inequality with K = -v / M
    have hK : 0 ≤ -v / M := div_nonneg (by linarith) hM.le
    have hneg : ∀ t : ℝ, -phi c t ≤ (-v / M) * w t := by
      intro t
      have h1 := hatom t
      have hpos : 0 < M * (1 + t^2) := by positivity
      have e : (-v / M) * w t = -v / (M * (1 + t^2)) := by
        unfold w; field_simp
      rw [e, le_div_iff₀ hpos]
      nlinarith
    have hineq := hd c (-v / M) hK hneg
    have e2 : -(-v / M * M) = v := by field_simp
    rw [e2] at hineq
    linarith
  -- pick an achievable point close to the meeting point
  obtain ⟨p, hpB, hpT⟩ := hmeet
  obtain ⟨y, hyA, hyd⟩ := Metric.mem_closure_iff.mp hpT δ hδ
  obtain ⟨a, ⟨ha0, ham⟩, rfl⟩ := hyA
  refine ⟨a, ha0, ham, fun q => ?_⟩
  have h1 : |traceMap n a q - p q| ≤ δ := by
    have := dist_le_pi_dist (traceMap n a) p q
    rw [dist_comm] at hyd
    rw [Real.dist_eq] at this
    linarith
  have h2 : |p q - R q| ≤ ε := by
    have := dist_le_pi_dist p r q
    rw [Metric.mem_closedBall] at hpB
    rw [Real.dist_eq] at this
    simp only [r] at this
    linarith
  calc |traceMap n a q - R q| = |(traceMap n a q - p q) + (p q - R q)| := by ring_nf
    _ ≤ |traceMap n a q - p q| + |p q - R q| := abs_add_le _ _
    _ ≤ δ + ε := add_le_add h1 h2
    _ = ε + δ := by ring

/-- The exact converse: for a positive budget, the prime-side inequality at tolerance `ε` is
equivalent to weighted stage solutions at every tolerance above `ε`. -/
theorem weightedFeasible_iff_dualIneq {R : ℚ → ℝ} {M ε : ℝ} {n : ℕ} (hM : 0 < M) (hε : 0 ≤ ε) :
    (∀ δ : ℝ, 0 < δ → WeightedFeasible R M (ε + δ) n) ↔ DualIneq R M ε n := by
  constructor
  · intro h c K hK hneg
    have hall : ∀ δ : ℝ, 0 < δ →
        -(K * M) - ε * ∑ q : S n, |c q| ≤ ∑ q : S n, c q * R q + δ * ∑ q : S n, |c q| := by
      intro δ hδ
      have := dualIneq_of_weightedFeasible (h δ hδ) c K hK hneg
      linarith
    have hs : 0 ≤ ∑ q : S n, |c q| := Finset.sum_nonneg (fun q _ => abs_nonneg _)
    by_contra hlt
    push_neg at hlt
    rcases hs.eq_or_lt with h0 | hpos
    · have := hall 1 one_pos
      rw [← h0] at this hlt
      linarith
    · set gap := -(K * M) - ε * ∑ q : S n, |c q| - ∑ q : S n, c q * R q
      have hgap : 0 < gap := by simp only [gap]; linarith
      have := hall (gap / (2 * ∑ q : S n, |c q|)) (by positivity)
      have e : gap / (2 * ∑ q : S n, |c q|) * ∑ q : S n, |c q| = gap / 2 := by
        rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hpos.ne']
      rw [e] at this
      simp only [gap] at this hgap
      linarith
  · intro hd δ hδ
    exact weightedFeasible_of_dualIneq hM hε hd hδ

end FleetDualConverse
