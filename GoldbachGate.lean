import Mathlib
import FibonacciCore

/-!
# The "42 Gate": axioms eliminated

`phi-spectral-framework/Certification.lean` states four results as `axiom`s
with the excuse *"COMPUTATIONAL WITNESS: verified by #eval, kernel reduction
infeasible"*, and the repo's headline theorem `forty_two_is_first_gate` is
literally `exact ⟨no_tunnels_before_42, forty_two_has_tunnel, …⟩` — i.e. an
axiom restatement, not a proof.

Three of those four are **decidable finite statements** and are proven here
by kernel evaluation (`decide`), and the fourth (`phi_pow_lt_seven_bound`)
is proven by interval arithmetic. Combined with `FibonacciCore`'s
`sqrt5_irrational` and `fib_ratio_tendsto_phi` — which replace two more
axioms from the same file — this eliminates **6 of that file's 10 axioms**,
so its "AXIOM-FREE" claim can become true rather than aspirational.

Definitions below are copied verbatim (up to notation) from
`Certification.lean` so the statements proven are the same statements.
-/

noncomputable section
open FibonacciCore

namespace GoldbachGate

/-! ## Rational scaffolding (verbatim from Certification.lean) -/

def pi7_rational : ℚ := 21991 / 1000

def entropy_rational : ℚ := 411246 / 10000

def spectral_phase_rat (k : ℕ) : ℚ := (k : ℚ) * pi7_rational / entropy_rational

def is_prime_small (n : ℕ) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else
    let limit := n.sqrt + 1
    let odd_divisors := (List.range ((limit - 3) / 2 + 1)).map (fun i => 3 + 2 * i)
    odd_divisors.all (fun d => d ≥ limit || n % d ≠ 0)

def find_goldbach_pairs (n : ℕ) : List (ℕ × ℕ) :=
  if n < 4 then []
  else
    let candidates := (List.range (n / 2 + 1)).filter (fun p => p ≥ 2)
    candidates.filterMap fun p =>
      let q := n - p
      if is_prime_small p && is_prime_small q then some (p, q) else none

def spectrally_aligned (p q : ℕ) (tolerance_num tolerance_den : ℕ) : Bool :=
  let phase_p := spectral_phase_rat p
  let phase_q := spectral_phase_rat q
  let combined := phase_p + phase_q
  let pi7 := pi7_rational
  let residue := combined - pi7 * (combined / pi7).floor
  let tolerance : ℚ := tolerance_num / tolerance_den
  (residue < tolerance) || ((pi7 - residue) < tolerance)

def has_goldbach_tunnel (n : ℕ) (tol_num tol_den : ℕ) : Bool :=
  let pairs := find_goldbach_pairs n
  pairs.any fun (p, q) => spectrally_aligned p q tol_num tol_den

/-! ## The three "computational witness" axioms, proven

**Trust note, stated up front.** Plain `decide` (elaborator-side reduction)
does not work here: `Rat` arithmetic and `Nat.sqrt` go through well-founded
recursion that the elaborator's `whnf` will not unfold. `decide +kernel`
does: the proposition is reduced by the Lean **kernel** itself (with its
GMP-accelerated `Nat` arithmetic) and the resulting `Decidable.decide p =
true` is checked as an ordinary term. No compiled evaluator is involved, so
— unlike the `native_decide` used in earlier revisions — these theorems
depend only on `[propext, Classical.choice, Quot.sound]`. `AxiomAudit.lean`
prints exactly that. -/

/-- Replaces `axiom five_thirtyseven_spectral`.
Axioms: `[propext, Classical.choice, Quot.sound]`. -/
theorem five_thirtyseven_spectral : spectrally_aligned 5 37 1 2 = true := by
  decide +kernel

/-- Replaces `axiom forty_two_has_tunnel`.
Axioms: `[propext, Classical.choice, Quot.sound]`. -/
theorem forty_two_has_tunnel : has_goldbach_tunnel 42 1 2 = true := by
  decide +kernel

/-- Replaces `axiom no_tunnels_before_42`. The bounded quantifier is turned
into a `List.all` over the finite range, then evaluated. -/
theorem no_tunnels_before_42_list :
    ((List.range 42).filter (fun m => decide (4 ≤ m) && decide (m % 2 = 0))).all
      (fun m => !has_goldbach_tunnel m 1 2) = true := by
  decide +kernel

theorem no_tunnels_before_42 :
    ∀ n : ℕ, 4 ≤ n → n < 42 → Even n → has_goldbach_tunnel n 1 2 = false := by
  have hlist := no_tunnels_before_42_list
  intro n h4 h42 heven
  have hmem : n ∈ (List.range 42).filter
      (fun m => decide (4 ≤ m) && decide (m % 2 = 0)) := by
    rw [List.mem_filter]
    refine ⟨List.mem_range.mpr h42, ?_⟩
    have hmod : n % 2 = 0 := Nat.even_iff.mp heven
    simp [h4, hmod]
  have := List.all_eq_true.mp hlist n hmem
  simpa using this

/-- **THE FIRST GATE, actually proven.** The original
`forty_two_is_first_gate` discharged this by `exact ⟨axiom, axiom, thm⟩`;
every component here is a theorem. -/
theorem forty_two_is_first_gate :
    (∀ n : ℕ, 4 ≤ n → n < 42 → Even n → has_goldbach_tunnel n 1 2 = false)
    ∧ has_goldbach_tunnel 42 1 2 = true
    ∧ Nat.Prime 5 ∧ Nat.Prime 37 ∧ 5 + 37 = 42 :=
  ⟨no_tunnels_before_42, forty_two_has_tunnel, by norm_num, by norm_num, by norm_num⟩

/-! ## `phi_pow_lt_seven_bound`, proven -/

/-- Tighter upper bound: `√5 < 2.2361` (needed because `φ^6 ≈ 17.944` is
close to 18 — a 1.62 bound is not enough, since `1.62^6 > 18`). -/
lemma sqrt5_upper_tight : Real.sqrt 5 < 2.2361 := by
  have h : (5 : ℝ) < 2.2361 ^ 2 := by norm_num
  calc Real.sqrt 5 < Real.sqrt (2.2361 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h
    _ = 2.2361 := Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.2361)

lemma phi_lt : phi < 1.61805 := by
  unfold phi
  have h := sqrt5_upper_tight
  linarith

lemma phi_nonneg : (0:ℝ) ≤ phi := le_of_lt (by
  unfold phi
  have := sqrt5_pos
  linarith)

/-- Replaces `axiom phi_pow_lt_seven_bound`: `φ^k < 18` for `k < 7`,
proven by interval arithmetic instead of asserted. -/
theorem phi_pow_lt_seven_bound (k : ℕ) (hk : k < 7) : phi ^ k < 18 := by
  have hub : phi < 1.61805 := phi_lt
  have hnn : (0:ℝ) ≤ phi := phi_nonneg
  have hmono : phi ^ k ≤ (1.61805 : ℝ) ^ 6 := by
    calc phi ^ k ≤ (1.61805 : ℝ) ^ k := pow_le_pow_left₀ hnn (le_of_lt hub) k
      _ ≤ (1.61805 : ℝ) ^ 6 := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
  have : (1.61805 : ℝ) ^ 6 < 18 := by norm_num
  linarith

end GoldbachGate
