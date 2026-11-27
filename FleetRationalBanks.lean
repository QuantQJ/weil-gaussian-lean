import Mathlib

namespace FleetRationalBanks
open Filter

/-- All fractions p/q with |p| ≤ n and 1 ≤ q ≤ n; duplicate fractions are removed. -/
def bank (n : ℕ) : Finset ℚ :=
  ((Finset.Icc (-(n : ℤ)) n).product (Finset.Icc 1 n)).image
    (fun pq : ℤ × ℕ => (pq.1 : ℚ) / pq.2)

lemma mem_bank {n : ℕ} {r : ℚ} : r ∈ bank n ↔
    ∃ p : ℤ, ∃ q : ℕ, -(n : ℤ) ≤ p ∧ p ≤ n ∧ 1 ≤ q ∧ q ≤ n ∧
      (p : ℚ)/q = r := by
  constructor
  · intro hr
    obtain ⟨⟨p,q⟩, hpq, he⟩ := Finset.mem_image.mp hr
    have hh := Finset.mem_product.mp hpq
    have hp := Finset.mem_Icc.mp hh.1
    have hq := Finset.mem_Icc.mp hh.2
    exact ⟨p,q,hp.1,hp.2,hq.1,hq.2,he⟩
  · rintro ⟨p,q,hp,hp',hq,hq',he⟩
    apply Finset.mem_image.mpr
    exact ⟨(p,q), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp,hp'⟩, Finset.mem_Icc.mpr ⟨hq,hq'⟩⟩,he⟩

lemma monotone_bank : Monotone bank := by
  intro n m hnm r hr
  obtain ⟨p,q,hp,hp',hq,hq',he⟩ := mem_bank.mp hr
  apply mem_bank.mpr
  refine ⟨p,q,?_,?_,hq,hq'.trans hnm,he⟩
  · exact (neg_le_neg (by exact_mod_cast hnm)).trans hp
  · exact hp'.trans (by exact_mod_cast hnm)

/-- A concrete stage containing a rational, obtained from its reduced representation. -/
def stage (r : ℚ) : ℕ := max r.num.natAbs r.den

lemma mem_bank_stage (r : ℚ) : r ∈ bank (stage r) := by
  apply mem_bank.mpr
  refine ⟨r.num,r.den,?_,?_,r.den_pos,le_max_right _ _,Rat.num_div_den r⟩
  · have hh : |r.num| ≤ (stage r : ℤ) := by
      change |r.num| ≤ ((max r.num.natAbs r.den : ℕ) : ℤ)
      simpa only [Int.natCast_natAbs] using
        (Int.ofNat_le.mpr (le_max_left r.num.natAbs r.den))
    exact (abs_le.mp hh).1
  · have hh : |r.num| ≤ (stage r : ℤ) := by
      change |r.num| ≤ ((max r.num.natAbs r.den : ℕ) : ℤ)
      simpa only [Int.natCast_natAbs] using
        (Int.ofNat_le.mpr (le_max_left r.num.natAbs r.den))
    exact (abs_le.mp hh).2

lemma mem_bank_of_stage_le (r : ℚ) {n : ℕ} (hn : stage r ≤ n) : r ∈ bank n :=
  monotone_bank hn (mem_bank_stage r)

lemma eventually_mem_bank (r : ℚ) : ∀ᶠ n in atTop, r ∈ bank n :=
  (eventually_ge_atTop (stage r)).mono fun _ hn => mem_bank_of_stage_le r hn

end FleetRationalBanks
