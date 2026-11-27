import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Under-constrained range proofs at the real BN254 scalar field

No `Fact p.Prime` anywhere: the exploit is a *ring* fact, so it instantiates at
the actual 254-bit BN254 scalar modulus with no primality certificate and no
`decide` call. Width is a parameter, so 64-bit is one instantiation.
-/

set_option autoImplicit false

namespace ZKBN254

/-- The BN254 (alt_bn128) scalar field modulus r. -/
def r : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

abbrev F := ZMod r

instance : NeZero r := ⟨by unfold r; norm_num⟩

/-- Horner evaluation of a bit list: `b₀ + 2·(b₁ + 2·(…))` = `∑ bᵢ 2ⁱ`.
This is exactly what a bit-decomposition circuit constrains. -/
def weightedSum {q : ℕ} (bits : List (ZMod q)) : ZMod q :=
  bits.foldr (fun b acc => b + 2 * acc) 0

@[simp] lemma weightedSum_nil {q : ℕ} : weightedSum ([] : List (ZMod q)) = 0 := rfl

@[simp] lemma weightedSum_cons {q : ℕ} (b : ZMod q) (l : List (ZMod q)) :
    weightedSum (b :: l) = b + 2 * weightedSum l := rfl

/-- The constraint the vulnerable circuit omits. -/
def AllBoolean {q : ℕ} (bits : List (ZMod q)) : Prop :=
  ∀ b ∈ bits, b * (1 - b) = 0

lemma weightedSum_replicate_zero {q w : ℕ} :
    weightedSum (List.replicate w (0 : ZMod q)) = 0 := by
  induction w with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, weightedSum_cons, ih]; ring

/-- **The exploit, in its strongest form: the range proof is VACUOUS.**
Drop booleanity and *every* field element has a satisfying `w`-bit witness —
so a circuit advertising "x fits in w bits" proves nothing at all. -/
theorem range_proof_is_vacuous {q : ℕ} (w : ℕ) (hw : 0 < w) (x : ZMod q) :
    ∃ bits : List (ZMod q), bits.length = w ∧ weightedSum bits = x := by
  refine ⟨x :: List.replicate (w - 1) 0, ?_, ?_⟩
  · simp; omega
  · rw [weightedSum_cons, weightedSum_replicate_zero]; ring

/-- Instantiated at BN254, width 64: the real target. -/
theorem bn254_range64_vacuous (x : F) :
    ∃ bits : List F, bits.length = 64 ∧ weightedSum bits = x :=
  range_proof_is_vacuous 64 (by norm_num) x

/-- Concretely: a value far above `2^64` passes the "64-bit" check. -/
theorem bn254_huge_value_passes_range64 :
    ∃ bits : List F, bits.length = 64 ∧ weightedSum bits = ((2 : F) ^ 200) :=
  bn254_range64_vacuous _

/-- And the forging witness is non-boolean, so the dropped constraint is
precisely what separates the two. -/
theorem forging_witness_not_boolean (w : ℕ) :
    ¬ AllBoolean ((2 : F) :: List.replicate w (0 : F)) := by
  intro h
  have h2 := h 2 (by simp)
  have he : (2 : F) * (1 - 2) = -(2 : F) := by ring
  rw [he, neg_eq_zero] at h2
  have hc : ((2 : ℕ) : F) = 0 := by push_cast; exact h2
  have hd : r ∣ 2 := (CharP.cast_eq_zero_iff F r 2).mp hc
  have hle := Nat.le_of_dvd (by norm_num) hd
  unfold r at hle; norm_num at hle

end ZKBN254

#print axioms ZKBN254.range_proof_is_vacuous
#print axioms ZKBN254.bn254_range64_vacuous
#print axioms ZKBN254.bn254_huge_value_passes_range64
#print axioms ZKBN254.forging_witness_not_boolean
