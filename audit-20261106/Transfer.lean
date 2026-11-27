import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

/-! ## Target 1 (in-domain): the Merkle path multiplexer -/
namespace MerkleMux

def r : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617
abbrev F := ZMod r
instance : NeZero r := ⟨by unfold r; norm_num⟩

/-- What a Merkle-path circuit computes at each level. -/
def mux {q : ℕ} (bit left right : ZMod q) : ZMod q := (1 - bit) * left + bit * right

/-- With the selector constrained boolean, it selects. -/
theorem mux_zero {q : ℕ} (l rr : ZMod q) : mux 0 l rr = l := by simp [mux]
theorem mux_one  {q : ℕ} (l rr : ZMod q) : mux 1 l rr = rr := by simp [mux]

/-- **Exploit: drop booleanity and the node reaches ANY value.** So a forged
intermediate state can be made to match an existing root — a membership proof
for an asset you do not own. -/
theorem mux_reaches_anything (t : F) : ∃ bit : F, mux bit 0 1 = t :=
  ⟨t, by simp [mux]⟩

/-- Generic form: any target between any two distinct children. -/
theorem mux_reaches_anything_general {q : ℕ} (l rr t : ZMod q) (h : IsUnit (rr - l)) :
    ∃ bit : ZMod q, mux bit l rr = t := by
  obtain ⟨u, hu⟩ := h
  refine ⟨(t - l) * (↑u⁻¹ : ZMod q), ?_⟩
  have hne : (rr - l) * (↑u⁻¹ : ZMod q) = 1 := by
    rw [← hu]; exact u.mul_inv
  simp only [mux]
  linear_combination (t - l) * hne

end MerkleMux

/-! ## Target 2 (out-of-domain): your own Python, DCA1225 analytics.py:547 -/
namespace DCANpv

/-- `analytics.py:547`:  `npv = eur_remaining * oil_price_usd * 0.7`
emitted under the field name `pv10_per_bbl`, comment "Simple NPV (10% discount)". -/
noncomputable def dcaNpv (eur price : ℝ) : ℝ := eur * price * 0.7

/-- An actual PV10: a level cashflow discounted at 10% over `n` periods. -/
noncomputable def pv10 (cash : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, cash / (1.1 : ℝ) ^ (i + 1)

/-- **The code cannot be a PV10.** A real discounted value depends on the
horizon; `dcaNpv` has no horizon argument, so no choice of its inputs can match
a PV10 at two different horizons. The label is wrong, provably. -/
theorem dcaNpv_cannot_be_pv10 (cash : ℝ) (hc : 0 < cash) (eur price : ℝ) :
    ¬ (dcaNpv eur price = pv10 cash 1 ∧ dcaNpv eur price = pv10 cash 2) := by
  rintro ⟨h1, h2⟩
  have hsame : pv10 cash 1 = pv10 cash 2 := by rw [← h1, ← h2]
  rw [pv10, pv10] at hsame
  simp [Finset.sum_range_succ] at hsame
  rcases hsame with h | h
  · exact hc.ne' h
  · norm_num at h

end DCANpv

#print axioms MerkleMux.mux_reaches_anything
#print axioms MerkleMux.mux_reaches_anything_general
#print axioms DCANpv.dcaNpv_cannot_be_pv10
