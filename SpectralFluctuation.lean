import Mathlib
import XpSpectrum

/-!
# The fluctuation term of a Bohr–Sommerfeld spectrum is bounded

A Bohr–Sommerfeld spectrum for a quantization function `A` and offset `c` is a
strictly increasing sequence `λ_n` with `A (λ_n) = 2π (n + c)`, `A` monotone on
`[λ_0, ∞)`. For such a spectrum the eigenvalue counting function
`N(E) = #{n | λ_n ≤ E}` differs from the smooth term `A(E)/(2π) − c` by at most
`1` for every `E ≥ λ_0` (`abs_fluct_le_one`), provided `λ_n → ∞`. So the
fluctuation `S(E) := N(E) − (A(E)/(2π) − c)` is *bounded* (`fluct_bounded`).

**Proven here (no axioms beyond Mathlib's):** the bound `|S(E)| ≤ 1`, the
resulting obstruction `not_bohrSommerfeld_of_unbounded_fluct` (a sequence with
unbounded fluctuation is not a Bohr–Sommerfeld spectrum for any `(A, c)`), and
uniqueness of the spectrum when `A` is injective.

**Only a hypothesis (NOT proven here):** the unboundedness of the Riemann
`S(T)` (Littlewood 1924 / Selberg). It enters `not_bohrSommerfeld_of_unbounded_fluct`
solely as the explicit assumption `hunb`. With `A = XpSpectrum.A`, the smooth
term is the Riemann–von Mangoldt main term, and the obstruction says: the zeta
ordinates are not a Bohr–Sommerfeld spectrum of the `xp` area for any offset `c`.
-/

noncomputable section
open Real Set

namespace SpectralFluctuation

/-- A spectrum obtained from the quantization rule `A (λ_n) = 2π (n + c)`,
with `A` monotone from `λ_0` on. -/
structure BohrSommerfeld (A : ℝ → ℝ) (c : ℝ) where
  lam : ℕ → ℝ
  strictMono : StrictMono lam
  quant : ∀ n, A (lam n) = 2 * π * ((n : ℝ) + c)
  monoA : MonotoneOn A (Set.Ici (lam 0))

/-- Eigenvalue counting function: the number of `n` with `λ_n ≤ E`. -/
def count (lam : ℕ → ℝ) (E : ℝ) : ℕ := Set.ncard {n : ℕ | lam n ≤ E}

/-- The smooth (Weyl-type) counting term `A(E)/(2π) − c`. -/
def smoothCount (A : ℝ → ℝ) (c E : ℝ) : ℝ := A E / (2 * π) - c

/-- The fluctuation term `S(E) = N(E) − smooth(E)`. -/
def fluct (A : ℝ → ℝ) (c : ℝ) (lam : ℕ → ℝ) (E : ℝ) : ℝ :=
  (count lam E : ℝ) - smoothCount A c E

variable {A : ℝ → ℝ} {c : ℝ}

/-- (a) In the cell `[λ_k, λ_{k+1})` the counting function equals `k + 1`. -/
theorem count_eq_of_mem_cell (B : BohrSommerfeld A c) {k : ℕ} {E : ℝ}
    (h1 : B.lam k ≤ E) (h2 : E < B.lam (k + 1)) : count B.lam E = k + 1 := by
  have hset : {n : ℕ | B.lam n ≤ E} = Set.Iic k := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    constructor
    · intro hn
      by_contra hnk
      push_neg at hnk
      have hk1 : k + 1 ≤ n := hnk
      have : B.lam (k + 1) ≤ B.lam n := B.strictMono.monotone hk1
      linarith
    · intro hn
      exact le_trans (B.strictMono.monotone hn) h1
  unfold count
  rw [hset, ← Finset.coe_Iic, Set.ncard_coe_finset, Nat.card_Iic]

/-- (b) In the cell `[λ_k, λ_{k+1})` the fluctuation lies in `[0, 1]`. -/
theorem fluct_bounded_of_mem_cell (B : BohrSommerfeld A c) {k : ℕ} {E : ℝ}
    (h1 : B.lam k ≤ E) (h2 : E < B.lam (k + 1)) :
    0 ≤ fluct A c B.lam E ∧ fluct A c B.lam E ≤ 1 := by
  have hcount := count_eq_of_mem_cell B h1 h2
  have hpi : 0 < 2 * π := by positivity
  have hk0 : B.lam 0 ≤ B.lam k := B.strictMono.monotone (Nat.zero_le k)
  have hkE : B.lam k ∈ Set.Ici (B.lam 0) := hk0
  have hEE : E ∈ Set.Ici (B.lam 0) := le_trans hk0 h1
  have hk1E : B.lam (k + 1) ∈ Set.Ici (B.lam 0) :=
    B.strictMono.monotone (Nat.zero_le (k + 1))
  have hlo : A (B.lam k) ≤ A E := B.monoA hkE hEE h1
  have hhi : A E ≤ A (B.lam (k + 1)) := B.monoA hEE hk1E (le_of_lt h2)
  rw [B.quant k] at hlo
  rw [B.quant (k + 1)] at hhi
  push_cast at hhi
  -- k + c ≤ A E / (2π) ≤ k + 1 + c
  have hlo' : (k : ℝ) + c ≤ A E / (2 * π) := by
    rw [le_div_iff₀ hpi]; linarith
  have hhi' : A E / (2 * π) ≤ (k : ℝ) + 1 + c := by
    rw [div_le_iff₀ hpi]; linarith
  unfold fluct smoothCount
  rw [hcount]
  push_cast
  constructor <;> linarith

/-- (c) Every `E ≥ λ_0` lies in some cell `[λ_k, λ_{k+1})`, provided `λ_n → ∞`. -/
theorem exists_cell (B : BohrSommerfeld A c)
    (hlim : Filter.Tendsto B.lam Filter.atTop Filter.atTop) {E : ℝ}
    (hE : B.lam 0 ≤ E) : ∃ k, B.lam k ≤ E ∧ E < B.lam (k + 1) := by
  classical
  have hex : ∃ n : ℕ, E < B.lam n := by
    obtain ⟨i, hi⟩ := Filter.tendsto_atTop_atTop.mp hlim (E + 1)
    exact ⟨i, by linarith [hi i le_rfl]⟩
  set m := Nat.find hex with hm
  have hspec : E < B.lam m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hspec
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨k, ?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    have : m ≤ k := Nat.find_min' hex hlt
    omega
  · rw [hk] at hspec; exact hspec

/-- (d) MAIN: for every `E ≥ λ_0`, `|S(E)| ≤ 1`. -/
theorem abs_fluct_le_one (B : BohrSommerfeld A c)
    (hlim : Filter.Tendsto B.lam Filter.atTop Filter.atTop) {E : ℝ}
    (hE : B.lam 0 ≤ E) : |fluct A c B.lam E| ≤ 1 := by
  obtain ⟨k, h1, h2⟩ := exists_cell B hlim hE
  obtain ⟨h0, h1'⟩ := fluct_bounded_of_mem_cell B h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- (e) The fluctuation of a Bohr–Sommerfeld spectrum is bounded on `[λ_0, ∞)`. -/
theorem fluct_bounded (B : BohrSommerfeld A c)
    (hlim : Filter.Tendsto B.lam Filter.atTop Filter.atTop) :
    ∃ K : ℝ, ∀ E ≥ B.lam 0, |fluct A c B.lam E| ≤ K :=
  ⟨1, fun _ hE => abs_fluct_le_one B hlim hE⟩

/-- (f) OBSTRUCTION: a sequence whose fluctuation is unbounded on `[γ_0, ∞)` is
not the spectrum of any Bohr–Sommerfeld quantization of `(A, c)` with `λ_n → ∞`. -/
theorem not_bohrSommerfeld_of_unbounded_fluct {γ : ℕ → ℝ}
    (hunb : ∀ K : ℝ, ∃ E ≥ γ 0, K < |fluct A c γ E|)
    (B : BohrSommerfeld A c)
    (hlim : Filter.Tendsto B.lam Filter.atTop Filter.atTop) : B.lam ≠ γ := by
  intro heq
  obtain ⟨E, hE, hK⟩ := hunb 1
  rw [← heq] at hE hK
  have := abs_fluct_le_one B hlim hE
  linarith

/-- (g) UNIQUENESS: two Bohr–Sommerfeld spectra for the same `(A, c)` coincide
whenever `A` is injective from the smaller of the two starting points on. -/
theorem lam_unique (B₁ B₂ : BohrSommerfeld A c)
    (hinj : Set.InjOn A (Set.Ici (min (B₁.lam 0) (B₂.lam 0)))) :
    B₁.lam = B₂.lam := by
  funext n
  have h1 : B₁.lam n ∈ Set.Ici (min (B₁.lam 0) (B₂.lam 0)) :=
    le_trans (min_le_left _ _) (B₁.strictMono.monotone (Nat.zero_le n))
  have h2 : B₂.lam n ∈ Set.Ici (min (B₁.lam 0) (B₂.lam 0)) :=
    le_trans (min_le_right _ _) (B₂.strictMono.monotone (Nat.zero_le n))
  apply hinj h1 h2
  rw [B₁.quant n, B₂.quant n]

/-- (h) Specialization to the Berry–Keating area `A(E) = E log E − E + 1`
(`XpSpectrum.A`). With this `A`, `smoothCount` is the Riemann–von Mangoldt
smooth term (up to the offset `c`), so for the zeta ordinates `γ` the
fluctuation `fluct XpSpectrum.A c γ` is `S(T)` up to a constant. Since `S(T)`
is unbounded (Littlewood/Selberg — cited, not proven here),
`not_bohrSommerfeld_of_unbounded_fluct` shows the zeros are not a
Bohr–Sommerfeld spectrum of the `xp` area for any offset `c`. -/
theorem berryKeating_fluct_le_one (c : ℝ) (B : BohrSommerfeld XpSpectrum.A c)
    (h0 : 1 ≤ B.lam 0)
    (hlim : Filter.Tendsto B.lam Filter.atTop Filter.atTop) {E : ℝ}
    (hE : B.lam 0 ≤ E) : |fluct XpSpectrum.A c B.lam E| ≤ 1 :=
  abs_fluct_le_one B hlim hE

/-- For the Berry–Keating area, the monotonicity field of `BohrSommerfeld` is
automatic once `1 ≤ λ_0`, via `XpSpectrum.A_strictMonoOn`. -/
theorem berryKeating_monoA_of_one_le {lam : ℕ → ℝ} (h0 : 1 ≤ lam 0) :
    MonotoneOn XpSpectrum.A (Set.Ici (lam 0)) :=
  (XpSpectrum.A_strictMonoOn.monotoneOn).mono (Set.Ici_subset_Ici.mpr h0)

end SpectralFluctuation
