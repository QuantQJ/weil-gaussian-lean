import HolderEquicontinuity
import SelfAdjointness
import Mathlib

/-!
# 1-D Rellich–Kondrachov and discreteness of the spectrum

`HolderEquicontinuity` proved the two Arzelà–Ascoli inputs for an `H¹` ball:
uniform boundedness and a uniform Hölder-½ modulus. This module applies
Mathlib's Arzelà–Ascoli theorem (`BoundedContinuousFunction.arzela_ascoli`)
to conclude the **compact embedding** `H¹₀(0,L) ↪ C[0,L] ↪ L²(0,L)` in
sequence form, and then draws the spectral consequence **without any
self-adjointness or resolvent theory**:

* `uniform_subseq` — every sequence with bounded energy `∫(u_n')² ≤ C` has
  a subsequence converging **uniformly** on `[0,L]` (Rellich–Kondrachov, 1-D).
* `l2_cauchy_subseq` — that subsequence is Cauchy in `L²`.
* `no_infinite_orthonormal_eigen_below` — for `H = −d²/dx² + V` with `V`
  bounded and continuous, there is **no infinite orthonormal family of
  eigenfunctions with eigenvalues ≤ Λ**, for any `Λ`. Energy of a normalized
  eigenfunction is `λ − ∫Vu² ≤ Λ + M`, so the family is bounded in `H¹`, so
  it has an `L²`-Cauchy subsequence — but orthonormal vectors are at mutual
  `L²`-distance `√2`.
* `eigenvalues_tendsto_atTop` — hence along any infinite orthonormal
  eigen-sequence the eigenvalues tend to `+∞`: the spectrum is discrete
  with finite multiplicities, accumulating only at `+∞`.

This is the discreteness half of "self-adjoint with discrete spectrum",
obtained directly from compactness. No `sorry`, no custom axioms.
-/

noncomputable section
open MeasureTheory Set intervalIntegral Filter Topology BoundedContinuousFunction

namespace RellichKondrachov

variable {L : ℝ}

/-! ## `H2` functions as bounded continuous functions on `[0,L]` -/

/-- The restriction of `u ∈ H²∩H¹₀(0,L)` to `[0,L]`, as a bounded continuous
function on the compact space `Icc 0 L`. -/
def toBCF (u : H2 L) : Icc (0:ℝ) L →ᵇ ℝ :=
  mkOfCompact ⟨(Icc (0:ℝ) L).restrict u.f,
    continuousOn_iff_continuous_restrict.mp u.hf_cont⟩

@[simp] lemma toBCF_apply (u : H2 L) (x : Icc (0:ℝ) L) : toBCF u x = u.f x := rfl

/-! ## Compact embedding: uniformly convergent subsequences -/

/-- **1-D Rellich–Kondrachov (sequence form).** A sequence in `H²∩H¹₀(0,L)`
with uniformly bounded energy `∫₀ᴸ (u_n')² ≤ C` has a subsequence that
converges **uniformly** on `[0,L]` to a continuous limit. -/
theorem uniform_subseq (hL : 0 < L) {C : ℝ} (u : ℕ → H2 L)
    (hC : ∀ n, (∫ t in (0)..L, (deriv (u n).f t) ^ 2) ≤ C) :
    ∃ g : Icc (0:ℝ) L →ᵇ ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x : Icc (0:ℝ) L, |(u (φ n)).f x - g x| < ε := by
  set A : Set (Icc (0:ℝ) L →ᵇ ℝ) := Set.range (fun n => toBCF (u n)) with hA
  -- (1) values lie in a compact ball
  have in_s : ∀ (f : Icc (0:ℝ) L →ᵇ ℝ) (x : Icc (0:ℝ) L), f ∈ A →
      f x ∈ Metric.closedBall (0:ℝ) (Real.sqrt (L * C)) := by
    rintro f x ⟨n, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, toBCF_apply]
    exact HolderEquicontinuity.unif_bounded_of_deriv_bound hL (u n) (hC n) x.2
  -- (2) equicontinuity from the uniform Hölder modulus
  have H : Equicontinuous ((↑) : A → Icc (0:ℝ) L → ℝ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    have hδpos : 0 < (ε / (Real.sqrt C + 1)) ^ 2 := by positivity
    rw [Metric.eventually_nhds_iff]
    refine ⟨(ε / (Real.sqrt C + 1)) ^ 2, hδpos, ?_⟩
    intro x hx
    rintro ⟨f, n, rfl⟩
    show dist ((toBCF (u n)) x₀) ((toBCF (u n)) x) < ε
    rw [Real.dist_eq, toBCF_apply, toBCF_apply]
    have hh := HolderEquicontinuity.holder_uniform hL (u n) (hC n) x₀.2 x.2
    have hdx : |(x₀:ℝ) - x| < (ε / (Real.sqrt C + 1)) ^ 2 := by
      rw [Subtype.dist_eq, Real.dist_eq] at hx
      rwa [abs_sub_comm]
    have h1 : Real.sqrt |(x₀:ℝ) - x| < ε / (Real.sqrt C + 1) := by
      rw [Real.sqrt_lt' (by positivity)]; exact hdx
    have hs0 : 0 ≤ Real.sqrt |(x₀:ℝ) - x| := Real.sqrt_nonneg _
    have hC0 : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
    calc |(u n).f x₀ - (u n).f x|
        ≤ Real.sqrt C * Real.sqrt |(x₀:ℝ) - x| := hh
      _ ≤ (Real.sqrt C + 1) * Real.sqrt |(x₀:ℝ) - x| := by nlinarith
      _ < (Real.sqrt C + 1) * (ε / (Real.sqrt C + 1)) :=
          mul_lt_mul_of_pos_left h1 (by positivity)
      _ = ε := by field_simp
  -- (3) Arzelà–Ascoli: the closure of the family is compact
  have hcomp : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:ℝ) (Real.sqrt (L * C)))
      (isCompact_closedBall _ _) A in_s H
  -- (4) extract a convergent subsequence
  obtain ⟨g, -, φ, hφ, hconv⟩ :=
    hcomp.tendsto_subseq (x := fun n => toBCF (u n)) (fun n => subset_closure ⟨n, rfl⟩)
  refine ⟨g, φ, hφ, ?_⟩
  intro ε hε
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv ε hε
  refine ⟨N, fun n hn x => ?_⟩
  have := (dist_lt_iff_of_compact hε).mp (hN n hn) x
  simpa [Real.dist_eq, toBCF_apply] using this

/-- **`L²`-Cauchy subsequence.** The uniformly convergent subsequence of
`uniform_subseq` is Cauchy in `L²(0,L)`: this is the compactness of the
embedding `H¹₀ ↪ L²`. -/
theorem l2_cauchy_subseq (hL : 0 < L) {C : ℝ} (u : ℕ → H2 L)
    (hC : ∀ n, (∫ t in (0)..L, (deriv (u n).f t) ^ 2) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        (∫ x in (0)..L, ((u (φ m)).f x - (u (φ n)).f x) ^ 2) ≤ ε := by
  obtain ⟨g, φ, hφ, hunif⟩ := uniform_subseq hL u hC
  refine ⟨φ, hφ, ?_⟩
  intro ε hε
  set η : ℝ := Real.sqrt (ε / L) / 2 with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨N, hN⟩ := hunif η hηpos
  refine ⟨N, fun m hm n hn => ?_⟩
  have huIcc : Set.uIcc (0:ℝ) L = Icc 0 L := Set.uIcc_of_le hL.le
  -- pointwise: |u_m − u_n| < 2η on [0,L], so the square is ≤ ε/L
  have hpt : ∀ x ∈ Icc (0:ℝ) L,
      ((u (φ m)).f x - (u (φ n)).f x) ^ 2 ≤ ε / L := by
    intro x hx
    have h1 := hN m hm ⟨x, hx⟩
    have h2 := hN n hn ⟨x, hx⟩
    simp only [] at h1 h2
    have hd : |(u (φ m)).f x - (u (φ n)).f x| < 2 * η := by
      calc |(u (φ m)).f x - (u (φ n)).f x|
          = |((u (φ m)).f x - g ⟨x, hx⟩) - ((u (φ n)).f x - g ⟨x, hx⟩)| := by ring_nf
        _ ≤ |(u (φ m)).f x - g ⟨x, hx⟩| + |(u (φ n)).f x - g ⟨x, hx⟩| := abs_sub _ _
        _ < η + η := add_lt_add h1 h2
        _ = 2 * η := by ring
    have h2η : 2 * η = Real.sqrt (ε / L) := by rw [hη]; ring
    have hsq : ((u (φ m)).f x - (u (φ n)).f x) ^ 2 < (2 * η) ^ 2 := by
      rw [← sq_abs]
      exact pow_lt_pow_left₀ hd (abs_nonneg _) (by norm_num : (2:ℕ) ≠ 0)
    rw [h2η, Real.sq_sqrt (by positivity)] at hsq
    exact hsq.le
  have hint : IntervalIntegrable (fun x => ((u (φ m)).f x - (u (φ n)).f x) ^ 2) volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact ((u (φ m)).hf_cont.sub (u (φ n)).hf_cont).pow 2
  calc (∫ x in (0)..L, ((u (φ m)).f x - (u (φ n)).f x) ^ 2)
      ≤ ∫ x in (0)..L, (ε / L) :=
        intervalIntegral.integral_mono_on hL.le hint intervalIntegrable_const hpt
    _ = ε := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        field_simp

/-! ## Discreteness of the spectrum -/

/-- Energy identity for a normalized eigenfunction: `∫(u')² = λ − ∫Vu²`, hence
`∫(u')² ≤ λ + M` when `|V| ≤ M`. -/
theorem energy_le_of_eigen (hL : 0 < L) (u : H2 L) (V : ℝ → ℝ) (M lam : ℝ)
    (hVcont : ContinuousOn V (Icc 0 L))
    (hVbound : ∀ x ∈ Icc 0 L, |V x| ≤ M)
    (hnorm : ∫ x in (0)..L, (u.f x) ^ 2 = 1)
    (heig : ∀ x ∈ Icc (0:ℝ) L, -(deriv (deriv u.f) x) + V x * u.f x = lam * u.f x) :
    (∫ t in (0)..L, (deriv u.f t) ^ 2) ≤ lam + M := by
  have huIcc : Set.uIcc (0:ℝ) L = Icc 0 L := Set.uIcc_of_le hL.le
  -- ∫(u')² = ∫(−u'')u
  have hkin := Semibounded.kinetic_energy_eq hL u
  -- ∫(−u'')u = ∫ (λu² − V u²)
  have hcongr : ∫ x in (0)..L, (-(deriv (deriv u.f) x)) * u.f x
      = ∫ x in (0)..L, (lam * (u.f x) ^ 2 - V x * (u.f x) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [huIcc] at hx
    simp only []
    have h := heig x hx
    have : -(deriv (deriv u.f) x) = lam * u.f x - V x * u.f x := by linarith
    rw [this]; ring
  have hi1 : IntervalIntegrable (fun x => lam * (u.f x) ^ 2) volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact (u.hf_cont.pow 2).const_smul lam
  have hi2 : IntervalIntegrable (fun x => V x * (u.f x) ^ 2) volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hVcont.mul (u.hf_cont.pow 2)
  have hsplit : ∫ x in (0)..L, (lam * (u.f x) ^ 2 - V x * (u.f x) ^ 2)
      = lam * (∫ x in (0)..L, (u.f x) ^ 2) - ∫ x in (0)..L, V x * (u.f x) ^ 2 := by
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul]
  -- ∫ V u² ≥ −M
  have hi3 : IntervalIntegrable (fun x => -M * (u.f x) ^ 2) volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact (u.hf_cont.pow 2).const_smul (-M)
  have hlow : (∫ x in (0)..L, -M * (u.f x) ^ 2) ≤ ∫ x in (0)..L, V x * (u.f x) ^ 2 := by
    apply intervalIntegral.integral_mono_on hL.le hi3 hi2
    intro x hx
    have hV := (abs_le.mp (hVbound x hx)).1
    have hu2 : 0 ≤ (u.f x) ^ 2 := sq_nonneg _
    nlinarith
  rw [intervalIntegral.integral_const_mul, hnorm, mul_one] at hlow
  rw [← hkin, hcongr, hsplit, hnorm, mul_one]
  linarith

/-- **No infinite orthonormal family of eigenfunctions below any level.**

For `H = −d²/dx² + V` on `(0,L)` with `V` bounded and continuous, and any
`Λ`, there is no sequence of mutually orthogonal, `L²`-normalized
eigenfunctions with eigenvalues `≤ Λ`. Proof: the energies are `≤ Λ + M`,
so by Rellich–Kondrachov some subsequence is `L²`-Cauchy — impossible, since
distinct orthonormal functions are at `L²`-distance `√2`.

This is the statement "the part of the spectrum below `Λ` has finite total
multiplicity", obtained with no self-adjointness and no resolvent. -/
theorem no_infinite_orthonormal_eigen_below (H : HPContinuum)
    (hVcont : ContinuousOn H.V (Icc 0 H.L)) (Λ : ℝ)
    (u : ℕ → H2 H.L) (lam : ℕ → ℝ)
    (heig : ∀ n, ∀ x ∈ Icc (0:ℝ) H.L,
      -(deriv (deriv (u n).f) x) + H.V x * (u n).f x = lam n * (u n).f x)
    (hΛ : ∀ n, lam n ≤ Λ)
    (hnorm : ∀ n, ∫ x in (0)..H.L, ((u n).f x) ^ 2 = 1)
    (horth : ∀ m n, m ≠ n → ∫ x in (0)..H.L, (u m).f x * (u n).f x = 0) :
    False := by
  obtain ⟨M, hM⟩ := H.hV_bounded
  have hL := H.hL
  have huIcc : Set.uIcc (0:ℝ) H.L = Icc 0 H.L := Set.uIcc_of_le hL.le
  -- bounded energy
  have hC : ∀ n, (∫ t in (0)..H.L, (deriv (u n).f t) ^ 2) ≤ Λ + M := by
    intro n
    have := energy_le_of_eigen hL (u n) H.V M (lam n) hVcont hM (hnorm n) (heig n)
    linarith [hΛ n]
  obtain ⟨φ, hφ, hcauchy⟩ := l2_cauchy_subseq hL u hC
  obtain ⟨N, hN⟩ := hcauchy 1 one_pos
  have hne : φ N ≠ φ (N + 1) := fun h => by
    have := hφ.injective h; omega
  have h := hN N le_rfl (N + 1) (Nat.le_succ N)
  -- ∫ (a − b)² = ∫a² − 2∫ab + ∫b² = 2
  set a := u (φ N)
  set b := u (φ (N + 1))
  have hia : IntervalIntegrable (fun x => (a.f x) ^ 2) volume 0 H.L := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact a.hf_cont.pow 2
  have hib : IntervalIntegrable (fun x => (b.f x) ^ 2) volume 0 H.L := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact b.hf_cont.pow 2
  have hiab : IntervalIntegrable (fun x => 2 * (a.f x * b.f x)) volume 0 H.L := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]
    exact continuousOn_const.mul (a.hf_cont.mul b.hf_cont)
  have hexp : ∫ x in (0)..H.L, (a.f x - b.f x) ^ 2
      = (∫ x in (0)..H.L, (a.f x) ^ 2) + (∫ x in (0)..H.L, (b.f x) ^ 2)
        - ∫ x in (0)..H.L, 2 * (a.f x * b.f x) := by
    rw [← intervalIntegral.integral_add hia hib,
      ← intervalIntegral.integral_sub (hia.add hib) hiab]
    apply intervalIntegral.integral_congr
    intro x _
    simp only []; ring
  rw [hexp, hnorm, hnorm, intervalIntegral.integral_const_mul, horth _ _ hne] at h
  linarith

/-- **Eigenvalues accumulate only at `+∞`.** Along any infinite orthonormal
sequence of eigenfunctions, `λ_n → +∞`. Equivalently: every level `Λ` is
exceeded by all but finitely many eigenvalues (counted with multiplicity).
This is the discreteness of the spectrum of `−d²/dx² + V` on a bounded
interval, from compactness alone. -/
theorem eigenvalues_tendsto_atTop (H : HPContinuum)
    (hVcont : ContinuousOn H.V (Icc 0 H.L))
    (u : ℕ → H2 H.L) (lam : ℕ → ℝ)
    (heig : ∀ n, ∀ x ∈ Icc (0:ℝ) H.L,
      -(deriv (deriv (u n).f) x) + H.V x * (u n).f x = lam n * (u n).f x)
    (hnorm : ∀ n, ∫ x in (0)..H.L, ((u n).f x) ^ 2 = 1)
    (horth : ∀ m n, m ≠ n → ∫ x in (0)..H.L, (u m).f x * (u n).f x = 0) :
    Tendsto lam atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro Λ
  by_contra hcon
  push_neg at hcon
  -- the set {n | lam n ≤ Λ} is infinite
  have hinf : Set.Infinite {n : ℕ | lam n ≤ Λ} := by
    intro hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    obtain ⟨n, hnN, hn⟩ := hcon (N + 1)
    have : n ≤ N := hN hn.le
    omega
  -- enumerate it and restrict the family to it
  let e := hinf.natEmbedding
  have he : ∀ k, lam (e k : ℕ) ≤ Λ := fun k => (e k).2
  have einj : Function.Injective (fun k => (e k : ℕ)) :=
    Subtype.val_injective.comp e.injective
  exact no_infinite_orthonormal_eigen_below H hVcont Λ
    (fun k => u (e k)) (fun k => lam (e k))
    (fun k => heig (e k)) he (fun k => hnorm (e k))
    (fun j k hjk => horth (e j) (e k) (fun h => hjk (einj h)))

end RellichKondrachov

end
