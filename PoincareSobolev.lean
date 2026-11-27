import Semibounded
import Mathlib

/-!
# Sobolev embedding, Poincaré, and coercivity

`Sobolev1D.lean` advertises in its header:

    2. Pointwise bound: |u(x)| ≤ √x · ‖u'‖₂ (Cauchy-Schwarz)
    3. Sup bound:       ‖u‖_∞ ≤ √L · ‖u'‖₂

Neither was ever proven — the file states them and moves on. This module
proves them, and then the two results they exist to support:

* **Poincaré inequality** `∫ u² ≤ L² ∫ (u')²` for `u ∈ H¹₀(0,L)`;
* **coercivity** `⟨Hu,u⟩ ≥ (1/L² − M)·∫u²`, so when `M·L² < 1` the operator
  is *positive definite*, not merely semibounded.

The Cauchy–Schwarz step is proven from scratch by the discriminant argument
(`sq_intervalIntegral_le`): `∫(f − t)² ≥ 0` for every `t` forces
`(∫f)² ≤ (b−a)·∫f²`. That avoids needing Mathlib's `L^p` duality machinery
and keeps the whole chain elementary.

No `sorry`, no custom axioms.
-/

noncomputable section
open MeasureTheory Set intervalIntegral

namespace PoincareSobolev

variable {L : ℝ}

/-! ## Cauchy–Schwarz against the constant function -/

/-- **Cauchy–Schwarz with unit weight**, by the discriminant argument:
`(∫_a^b f)² ≤ (b − a) · ∫_a^b f²`.

Proof: for every real `t`, `0 ≤ ∫ (f − t)² = ∫f² − 2t∫f + t²(b−a)`.
A quadratic in `t` that is everywhere nonnegative has nonpositive
discriminant, which is exactly the claim. -/
theorem sq_intervalIntegral_le {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, (f x) ^ 2 := by
  have huIcc : Set.uIcc a b = Icc a b := Set.uIcc_of_le hab
  have hfi : IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hf
  have hf2 : IntervalIntegrable (fun x => (f x) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hf.pow 2
  set A : ℝ := ∫ x in a..b, (f x) ^ 2 with hA
  set B : ℝ := ∫ x in a..b, f x with hB
  set C : ℝ := b - a with hC
  -- the quadratic inequality, for every t
  have key : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C := by
    intro t
    have hnn : 0 ≤ ∫ x in a..b, (f x - t) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
    have hexp : ∫ x in a..b, (f x - t) ^ 2
        = A - 2 * t * B + t ^ 2 * C := by
      have hsplit : ∀ x : ℝ, (f x - t) ^ 2
          = (f x) ^ 2 + (-(2 * t)) * f x + t ^ 2 := by
        intro x; ring
      have hi1 : IntervalIntegrable (fun x => (f x) ^ 2 + (-(2*t)) * f x) volume a b :=
        hf2.add (hfi.const_mul _)
      have hi2 : IntervalIntegrable (fun _ : ℝ => t ^ 2) volume a b :=
        intervalIntegrable_const
      calc ∫ x in a..b, (f x - t) ^ 2
          = ∫ x in a..b, ((f x) ^ 2 + (-(2*t)) * f x + t ^ 2) :=
            intervalIntegral.integral_congr (fun x _ => hsplit x)
        _ = (∫ x in a..b, ((f x) ^ 2 + (-(2*t)) * f x)) + ∫ x in a..b, (t ^ 2 : ℝ) :=
            intervalIntegral.integral_add hi1 hi2
        _ = ((∫ x in a..b, (f x) ^ 2) + (-(2*t)) * ∫ x in a..b, f x)
              + t ^ 2 * (b - a) := by
            rw [intervalIntegral.integral_add hf2 (hfi.const_mul _),
                intervalIntegral.integral_const_mul,
                intervalIntegral.integral_const]
            simp [smul_eq_mul, mul_comm]
        _ = A - 2 * t * B + t ^ 2 * C := by rw [hA, hB, hC]; ring
    rw [hexp] at hnn
    exact hnn
  -- discriminant: instantiate at the vertex
  rcases eq_or_lt_of_le (by linarith [hab] : (0:ℝ) ≤ C) with hC0 | hCpos
  · -- degenerate interval: both sides vanish
    have hba : a = b := by rw [hC] at hC0; linarith
    subst hba
    simp [hB, hA]
  · have h := key (B / C)
    have hCne : C ≠ 0 := ne_of_gt hCpos
    have hexp : A - 2 * (B / C) * B + (B / C) ^ 2 * C = A - B ^ 2 / C := by
      field_simp; ring
    rw [hexp] at h
    have hdiv : B ^ 2 / C ≤ A := by linarith
    rw [div_le_iff₀ hCpos] at hdiv
    linarith [hdiv]

/-! ## Sobolev embedding in one dimension -/

/-- **Pointwise Sobolev bound** (the file's stated Key Theorem 2):
`|u(x)|² ≤ x · ∫₀ˣ (u')²` for `u ∈ H¹₀(0,L)` and `0 ≤ x ≤ L`.

Immediate from the FTC representation `u(x) = ∫₀ˣ u'` and Cauchy–Schwarz. -/
theorem sobolev_pointwise_sq (_hL : 0 < L) (u : H2 L) {x : ℝ}
    (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    (u.f x) ^ 2 ≤ x * ∫ t in (0)..x, (deriv u.f t) ^ 2 := by
  have hrepr : u.f x = ∫ t in (0)..x, deriv u.f t :=
    H1zero.ftc_repr u.toH1zero x hx0 hxL
  have hcont : ContinuousOn (deriv u.f) (Icc 0 x) :=
    u.hdf_cont.mono (Icc_subset_Icc_right hxL)
  have h := sq_intervalIntegral_le hx0 hcont
  rw [hrepr]
  simpa using h

/-- Monotonicity of `∫ (u')²` in the upper limit (the integrand is `≥ 0`). -/
lemma deriv_sq_integral_mono (hL : 0 < L) (u : H2 L) {x : ℝ}
    (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    (∫ t in (0)..x, (deriv u.f t) ^ 2) ≤ ∫ t in (0)..L, (deriv u.f t) ^ 2 := by
  have huIcc : Set.uIcc (0:ℝ) L = Icc 0 L := Set.uIcc_of_le hL.le
  have hint : IntervalIntegrable (fun t => (deriv u.f t) ^ 2) volume 0 L := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact u.hdf_cont.pow 2
  have h1 : IntervalIntegrable (fun t => (deriv u.f t) ^ 2) volume 0 x :=
    hint.mono_set (by rw [Set.uIcc_of_le hx0, Set.uIcc_of_le hL.le]
                      exact Icc_subset_Icc_right hxL)
  have h2 : IntervalIntegrable (fun t => (deriv u.f t) ^ 2) volume x L :=
    hint.mono_set (by rw [Set.uIcc_of_le hxL, Set.uIcc_of_le hL.le]
                      exact Icc_subset_Icc_left hx0)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have htail : 0 ≤ ∫ t in x..L, (deriv u.f t) ^ 2 :=
    intervalIntegral.integral_nonneg hxL (fun t _ => sq_nonneg _)
  linarith [hadd, htail]

/-- **Sup bound** (the file's stated Key Theorem 3):
`|u(x)|² ≤ L · ∫₀ᴸ (u')²` uniformly on `[0,L]`, i.e. `‖u‖_∞ ≤ √L·‖u'‖₂`. -/
theorem sobolev_sup_bound (hL : 0 < L) (u : H2 L) {x : ℝ}
    (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    (u.f x) ^ 2 ≤ L * ∫ t in (0)..L, (deriv u.f t) ^ 2 := by
  have h1 := sobolev_pointwise_sq hL u hx0 hxL
  have h2 := deriv_sq_integral_mono hL u hx0 hxL
  have hK : 0 ≤ ∫ t in (0)..x, (deriv u.f t) ^ 2 :=
    intervalIntegral.integral_nonneg hx0 (fun t _ => sq_nonneg _)
  calc (u.f x) ^ 2 ≤ x * ∫ t in (0)..x, (deriv u.f t) ^ 2 := h1
    _ ≤ L * ∫ t in (0)..x, (deriv u.f t) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hxL hK
    _ ≤ L * ∫ t in (0)..L, (deriv u.f t) ^ 2 := by
        exact mul_le_mul_of_nonneg_left h2 hL.le

/-! ## Poincaré inequality -/

/-- **Poincaré inequality** for `H¹₀(0,L)`: `∫₀ᴸ u² ≤ L² ∫₀ᴸ (u')²`.

(The sharp constant is `(L/π)²`, attained by the first Dirichlet
eigenfunction; `L²` is what the elementary sup-bound route gives, and it is
enough for coercivity.) -/
theorem poincare (hL : 0 < L) (u : H2 L) :
    (∫ x in (0)..L, (u.f x) ^ 2) ≤ L ^ 2 * ∫ t in (0)..L, (deriv u.f t) ^ 2 := by
  have huIcc : Set.uIcc (0:ℝ) L = Icc 0 L := Set.uIcc_of_le hL.le
  set K : ℝ := ∫ t in (0)..L, (deriv u.f t) ^ 2 with hK
  have hu2 : IntervalIntegrable (fun x => (u.f x) ^ 2) volume 0 L := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact u.hf_cont.pow 2
  have hconst : IntervalIntegrable (fun _ : ℝ => L * K) volume 0 L :=
    intervalIntegrable_const
  have hmono : ∀ x ∈ Icc (0:ℝ) L, (u.f x) ^ 2 ≤ L * K := by
    intro x hx
    exact sobolev_sup_bound hL u hx.1 hx.2
  have := intervalIntegral.integral_mono_on hL.le hu2 hconst hmono
  rw [intervalIntegral.integral_const] at this
  simp only [smul_eq_mul, sub_zero] at this
  calc (∫ x in (0)..L, (u.f x) ^ 2) ≤ L * (L * K) := this
    _ = L ^ 2 * K := by ring

/-! ## Coercivity: from semibounded to positive definite -/

/-- **Coercivity.** For `H = −d²/dx² + V` with `|V| ≤ M`,

  `⟨Hu, u⟩ ≥ (1/L² − M) · ∫ u²`.

In particular when `M·L² < 1` the operator is **positive definite**, not
merely bounded below — the strongest form of the Friedrichs hypothesis, and
the condition under which the form defines an equivalent inner product on
`H¹₀`. -/
theorem hp_form_coercive (hL : 0 < L) (u : H2 L) (V : ℝ → ℝ) (M : ℝ)
    (hVcont : ContinuousOn V (Icc 0 L))
    (hVbound : ∀ x ∈ Icc 0 L, |V x| ≤ M) :
    (1 / L ^ 2 - M) * (∫ x in (0)..L, (u.f x) ^ 2)
      ≤ ∫ x in (0)..L, (-(deriv (deriv u.f) x) + V x * u.f x) * u.f x := by
  have huIcc : Set.uIcc (0:ℝ) L = Icc 0 L := Set.uIcc_of_le hL.le
  set K : ℝ := ∫ t in (0)..L, (deriv u.f t) ^ 2 with hK
  set S : ℝ := ∫ x in (0)..L, (u.f x) ^ 2 with hS
  -- kinetic part equals K
  have hkin : ∫ x in (0)..L, (-(deriv (deriv u.f) x)) * u.f x = K :=
    Semibounded.kinetic_energy_eq hL u
  -- potential part ≥ −M·S
  have hpot : IntervalIntegrable (fun x => V x * u.f x * u.f x) volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact (hVcont.mul u.hf_cont).mul u.hf_cont
  have hkinI : IntervalIntegrable
      (fun x => (-(deriv (deriv u.f) x)) * u.f x) volume 0 L :=
    u.hddf_int.neg.mul_continuousOn (by rw [huIcc]; exact u.hf_cont)
  have hsq : IntervalIntegrable (fun x => (u.f x) ^ 2) volume 0 L := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact u.hf_cont.pow 2
  have hMsq : IntervalIntegrable (fun x => -M * (u.f x) ^ 2) volume 0 L :=
    hsq.const_mul _
  have hpot_lb : -M * S ≤ ∫ x in (0)..L, V x * u.f x * u.f x := by
    have hmono : ∀ x ∈ Icc (0:ℝ) L, -M * (u.f x) ^ 2 ≤ V x * u.f x * u.f x := by
      intro x hx
      have hVge : -M ≤ V x := neg_le_of_abs_le (hVbound x hx)
      calc -M * (u.f x) ^ 2 ≤ V x * (u.f x) ^ 2 :=
            mul_le_mul_of_nonneg_right hVge (sq_nonneg _)
        _ = V x * u.f x * u.f x := by ring
    have := intervalIntegral.integral_mono_on hL.le hMsq hpot hmono
    rwa [intervalIntegral.integral_const_mul, ← hS] at this
  -- split the form
  have hsplit : ∫ x in (0)..L, (-(deriv (deriv u.f) x) + V x * u.f x) * u.f x
      = K + ∫ x in (0)..L, V x * u.f x * u.f x := by
    rw [← hkin, ← intervalIntegral.integral_add hkinI hpot]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  -- Poincaré: S ≤ L²K, i.e. K ≥ S/L²
  have hpoin : S ≤ L ^ 2 * K := poincare hL u
  have hL2 : (0:ℝ) < L ^ 2 := by positivity
  have hKlb : (1 / L ^ 2) * S ≤ K := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hL2]
    linarith [hpoin]
  rw [hsplit]
  linarith [hKlb, hpot_lb]

end PoincareSobolev
