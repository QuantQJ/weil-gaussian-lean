import Mathlib

/-!
# DeepMind's non-archimedean Weil factor = the von Mangoldt prime sum

`google-deepmind/formal-conjectures`, `Paper/RiemannHypothesisEquivalents.lean`, defines
`weilNonArchimedean p f = log p * Σ' m, exp (-(m+1) log p / 2) * (f ((m+1) log p) + f (-(m+1) log p))`.
For a compactly supported `f`, the sum over primes of this factor is the two-sided von Mangoldt sum
`Σ' n, Λ n * n^{-1/2} * (f (log n) + f (-log n))` used by hp-proof's explicit formula
(`GammaExplicitFormula.primeSum f + primeSum (reflect f)`). This is one piece of a proof of their
`weil_positivity_criterion`; the archimedean normalisation and the RH ⇔ positivity step are not done here.
-/

set_option autoImplicit false
noncomputable section
open scoped ArithmeticFunction

namespace FleetWeilNonArch

/-- DeepMind's definition, verbatim. -/
def weilNonArchimedean (p : ℕ) (f : ℝ → ℝ) : ℝ :=
  Real.log p * ∑' m : ℕ, Real.exp (-(m + 1) * Real.log p / 2) * (f ((m + 1) * Real.log p) + f (-(m + 1) * Real.log p))

/-- The two-sided von Mangoldt sum. -/
def vonMangoldtSum (f : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * (f (Real.log n) + f (-Real.log n))

/-- The term of the double sum at the prime power `p^(m+1)`. -/
def g (f : ℝ → ℝ) (x : Nat.Primes × ℕ) : ℝ :=
  Real.log (x.1 : ℕ) * (Real.exp (-(x.2 + 1) * Real.log (x.1 : ℕ) / 2)
    * (f ((x.2 + 1) * Real.log (x.1 : ℕ)) + f (-(x.2 + 1) * Real.log (x.1 : ℕ))))

lemma term_eq (f : ℝ → ℝ) (x : Nat.Primes × ℕ) :
    g f x = (fun n : ℕ => Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * (f (Real.log n) + f (-Real.log n)))
      ((x.1 : ℕ) ^ (x.2 + 1)) := by
  obtain ⟨⟨p, hp⟩, m⟩ := x
  simp only [g]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : Real.log ((p ^ (m + 1) : ℕ) : ℝ) = (m + 1) * Real.log p := by
    push_cast; rw [Real.log_pow]; push_cast; ring
  have hrpow : ((p ^ (m + 1) : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) = Real.exp (-(m + 1) * Real.log p / 2) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast pow_pos hp.pos _), hlog]; ring_nf
  rw [hlog, hrpow]
  ring_nf

lemma inj : Function.Injective (fun x : Nat.Primes × ℕ => (x.1 : ℕ) ^ (x.2 + 1)) := by
  rintro ⟨p, k⟩ ⟨q, j⟩ h
  obtain ⟨hpq, hkj⟩ := Nat.Prime.pow_inj p.2 q.2 h
  exact Prod.ext (Subtype.ext hpq) (by simpa using hkj)

lemma supp (f : ℝ → ℝ) :
    Function.support (fun n : ℕ => Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * (f (Real.log n) + f (-Real.log n)))
      ⊆ Set.range (fun x : Nat.Primes × ℕ => (x.1 : ℕ) ^ (x.2 + 1)) := by
  intro n hn
  have hΛ : Λ n ≠ 0 := fun h => hn (by simp [h])
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  exact ⟨(⟨p, hp⟩, k - 1), by simp only; congr 1; omega⟩

/-- **The identity**, for `f` vanishing outside `[-A, A]`: the sum over primes of DeepMind's
non-archimedean factors equals the two-sided von Mangoldt sum. -/
theorem sum_weilNonArchimedean_eq {f : ℝ → ℝ} {A : ℝ} (hf : ∀ x, A < |x| → f x = 0) :
    ∑' p : Nat.Primes, weilNonArchimedean p f = vonMangoldtSum f := by
  -- only finitely many prime powers contribute
  have hfin : (Function.support (g f)).Finite := by
    apply Set.Finite.subset ((Set.finite_Iio (⌈Real.exp A⌉₊ + 1)).preimage
      (inj.injOn) |>.subset (fun _ h => h))
    intro x hx
    simp only [Set.mem_preimage, Set.mem_Iio]
    by_contra hge; push_neg at hge
    apply hx
    rw [term_eq]
    have hn : Real.exp A < ((x.1 : ℕ) ^ (x.2 + 1) : ℕ) := by
      have := Nat.le_ceil (Real.exp A)
      have h2 : (⌈Real.exp A⌉₊ : ℝ) + 1 ≤ (((x.1 : ℕ) ^ (x.2 + 1) : ℕ) : ℝ) := by exact_mod_cast hge
      linarith
    have hpos : (0 : ℝ) < ((x.1 : ℕ) ^ (x.2 + 1) : ℕ) := lt_trans (Real.exp_pos A) hn
    have hL : A < Real.log (((x.1 : ℕ) ^ (x.2 + 1) : ℕ) : ℝ) := by
      rw [Real.lt_log_iff_exp_lt hpos]; exact hn
    have hL0 : 0 ≤ Real.log (((x.1 : ℕ) ^ (x.2 + 1) : ℕ) : ℝ) := by
      apply Real.log_nonneg; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ x.1.2.ne_zero)
    have h1 := hf (Real.log (((x.1 : ℕ) ^ (x.2 + 1) : ℕ) : ℝ)) (by rw [abs_of_nonneg hL0]; exact hL)
    have h2 := hf (-Real.log (((x.1 : ℕ) ^ (x.2 + 1) : ℕ) : ℝ)) (by rw [abs_neg, abs_of_nonneg hL0]; exact hL)
    simp only; rw [h1, h2]; ring
  have hsum : Summable (g f) := summable_of_hasFiniteSupport hfin
  unfold vonMangoldtSum
  rw [← inj.tsum_eq (supp f)]
  rw [show (fun c : Nat.Primes × ℕ => (fun n : ℕ => Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ)
      * (f (Real.log n) + f (-Real.log n))) ((c.1 : ℕ) ^ (c.2 + 1))) = g f from funext (fun x => (term_eq f x).symm)]
  rw [hsum.tsum_prod' (fun p => hsum.prod_factor p)]
  congr 1; funext p
  unfold weilNonArchimedean
  rw [← tsum_mul_left]
  rfl
