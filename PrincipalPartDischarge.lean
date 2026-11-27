import ContourShift
import LogDerivResidue
import ZetaLogDerivPole
import Residue
import RectangleResidue
import ZetaStrip
import ZerosCountable
import Mathlib

/-!
# Discharging the principal-part hypothesis of the contour-shift identity

`ContourShift.contour_shift_rectangle` needs a holomorphic remainder `H` on the closed
rectangle `R := [[1 - c, c]] ×ℂ [[-T, T]]` with
`ζ'/ζ (s) = H s + ∑ ρ ∈ Z, m ρ / (s − ρ) − 1 / (s − 1)` wherever `ζ s ≠ 0`, `s ≠ 1`.
This file constructs `Z`, `m` and `H`.

**Proven (no custom axioms):**

* `zeroFinset c T` — the zeros of `ζ` in the closed rectangle other than `1`, as a `Finset`
  (finiteness: `R` is compact and every zero of `ζ` is isolated, `finite_zeros_of_isCompact`).
* `zetaOrder ρ` — the order of vanishing of `ζ` at `ρ` (`analyticOrderAt`), with the local
  factorisation `ζ = (· − ρ)^{zetaOrder ρ} · g`, `g` analytic, `g ρ ≠ 0` (`exists_factorization`),
  and `0 < zetaOrder ρ` at a zero (`zetaOrder_pos`).
* `logDeriv_zeta_eventually_eq_near_one` — near `1`, `ζ'/ζ = −1/(s − 1) + N'/N` with
  `N = (s − 1)ζ` entire, `N 1 = 1`.
* `exists_differentiableAt_of_tendsto_punctures` — a general removable-singularity gluing lemma:
  a function differentiable off a finite puncture set with a limit at each puncture extends.
* `exists_holomorphic_remainder` — the target statement: `Z`, `m` and a holomorphic `H` with
  the identity above, i.e. hypothesis `hH` of `ContourShift.contour_shift_rectangle`, together
  with `hZ_one`, `hZ_all` and the characterisation of `Z`.
* `contour_shift_rectangle_of_G` — the contour-shift identity with `hH`, `hZ_one`, `hZ_all`,
  `hZ_in` discharged: only `hG` (holomorphy of `G`), `hF` (segment integrability) and
  `hbd` (no zero of `ζ` on the *boundary* of the closed rectangle) remain.

**Hypothesis-dependent:** `contour_shift_rectangle_of_G` keeps `hbd`, which is genuinely needed
(for `c = 3` the trivial zero `−2` lies on the left edge); it is *not* implied by `hF`.

**Not proven:** the `T → ∞` limit and the horizontal-segment bounds (outside the scope here).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Topology Set Interval
open scoped Real

namespace PrincipalPartDischarge

/-! ## Local structure of `ζ` at the pole `s = 1` -/

/-- The entire function `(s − 1) ζ(s)` (with the value `1` at `s = 1`):
`zetaNum s = (s − 1) · zetaReg s + Γℝ(s)⁻¹`. -/
def zetaNum (s : ℂ) : ℂ := (s - 1) * ZetaLogDerivPole.zetaReg s + (Gammaℝ s)⁻¹

/-- `zetaNum` is entire. -/
theorem differentiable_zetaNum : Differentiable ℂ zetaNum :=
  ((differentiable_id.sub_const 1).mul ZetaLogDerivPole.differentiable_zetaReg).add
    differentiable_Gammaℝ_inv

/-- `zetaNum 1 = 1`. -/
theorem zetaNum_one : zetaNum 1 = 1 := by
  simp [zetaNum, ZetaLogDerivPole.Gammaℝ_inv_one]

/-- For `s ≠ 1`, `ζ s = zetaNum s / (s − 1)`. -/
theorem riemannZeta_eq_zetaNum_div {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = zetaNum s / (s - 1) := by
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [ZetaLogDerivPole.riemannZeta_eq_zetaReg_add, zetaNum, add_div, mul_div_cancel_left₀ _ h]

/-- The derivative of `ζ` at `s ≠ 1`, via the quotient rule for `zetaNum / (s − 1)`. -/
theorem deriv_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta s = (deriv zetaNum s * (s - 1) - zetaNum s) / (s - 1) ^ 2 := by
  have hev : riemannZeta =ᶠ[𝓝 s] fun t => zetaNum t / (t - 1) := by
    filter_upwards [eventually_ne_nhds hs] with t ht
    exact riemannZeta_eq_zetaNum_div ht
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun t => zetaNum t / (t - 1))
      ((deriv zetaNum s * (s - 1) - zetaNum s * 1) / (s - 1) ^ 2) s :=
    (differentiable_zetaNum s).hasDerivAt.div ((hasDerivAt_id' s).sub_const 1)
      (sub_ne_zero.mpr hs)
  rw [hd.deriv]
  ring

/-- Near `s = 1`, the logarithmic derivative of `ζ` is `−1/(s − 1) + zetaNum'/zetaNum`. -/
theorem logDeriv_zeta_eventually_eq_near_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ), deriv riemannZeta s / riemannZeta s =
      (-1 : ℂ) / (s - 1) + deriv zetaNum s / zetaNum s := by
  have hne : ∀ᶠ s in 𝓝 (1 : ℂ), zetaNum s ≠ 0 :=
    (differentiable_zetaNum 1).continuousAt.eventually_ne (by rw [zetaNum_one]; exact one_ne_zero)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hne, self_mem_nhdsWithin] with s hs hs1
  have hs1' : s ≠ 1 := hs1
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1'
  rw [deriv_riemannZeta_of_ne_one hs1', riemannZeta_eq_zetaNum_div hs1']
  field_simp
  ring

/-! ## Isolated zeros and the finite zero set of the rectangle -/

/-- `ζ` is nonvanishing on a punctured neighbourhood of every point (including `1`, where
`(s − 1) ζ(s) → 1`). -/
theorem eventually_ne_zero_punctured (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, riemannZeta w ≠ 0 := by
  rcases eq_or_ne z 1 with rfl | hz
  · filter_upwards [riemannZeta_residue_one.eventually_ne one_ne_zero] with w hw
    exact right_ne_zero_of_mul hw
  · exact ZerosCountable.isolated_zero_riemannZeta hz

/-- The zeros of `ζ` other than `1` in a compact set form a finite set
(finite subcover by punctured neighbourhoods on which `ζ ≠ 0`). -/
theorem finite_zeros_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    {s : ℂ | s ∈ K ∧ s ≠ 1 ∧ riemannZeta s = 0}.Finite := by
  have hU : ∀ x ∈ K, {w : ℂ | w ≠ x → riemannZeta w ≠ 0} ∈ 𝓝 x := by
    intro x _
    have h : ∀ᶠ w in 𝓝 x, w ≠ x → riemannZeta w ≠ 0 :=
      eventually_nhdsWithin_iff.mp (eventually_ne_zero_punctured x)
    exact h
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover _ hU
  refine t.finite_toSet.subset ?_
  rintro s ⟨hsK, -, hs0⟩
  obtain ⟨x, hxt, hsx⟩ := Set.mem_iUnion₂.mp (ht hsK)
  rcases eq_or_ne s x with rfl | hne
  · exact hxt
  · exact absurd hs0 (hsx hne)

/-- The closed rectangle `[[1 − c, c]] ×ℂ [[−T, T]]` is compact. -/
theorem isCompact_rect (c T : ℝ) : IsCompact ([[1 - c, c]] ×ℂ [[-T, T]]) :=
  isCompact_uIcc.reProdIm isCompact_uIcc

/-- The finite set of zeros of `ζ` in the closed rectangle `[[1 − c, c]] ×ℂ [[−T, T]]`,
other than the point `1`. -/
def zeroFinset (c T : ℝ) : Finset ℂ :=
  (finite_zeros_of_isCompact (isCompact_rect c T)).toFinset

/-- Membership in `zeroFinset`. -/
theorem mem_zeroFinset {c T : ℝ} {ρ : ℂ} :
    ρ ∈ zeroFinset c T ↔ ρ ∈ [[1 - c, c]] ×ℂ [[-T, T]] ∧ ρ ≠ 1 ∧ riemannZeta ρ = 0 :=
  Set.Finite.mem_toFinset _

/-- `1 ∉ zeroFinset c T`. -/
theorem one_not_mem_zeroFinset (c T : ℝ) : (1 : ℂ) ∉ zeroFinset c T :=
  fun h => (mem_zeroFinset.mp h).2.1 rfl

/-! ## The order of vanishing and the local factorisation at a zero -/

/-- `ζ` is analytic at every `ρ ≠ 1`. -/
theorem analyticAt_riemannZeta_of_ne_one {ρ : ℂ} (hρ : ρ ≠ 1) : AnalyticAt ℂ riemannZeta ρ :=
  ZerosCountable.analyticOnNhd_riemannZeta ρ (Set.mem_compl_singleton_iff.mpr hρ)

/-- `ζ` does not vanish identically near any `ρ ≠ 1`. -/
theorem not_eventually_zero {ρ : ℂ} (hρ1 : ρ ≠ 1) : ¬ ∀ᶠ z in 𝓝 ρ, riemannZeta z = 0 := by
  intro hev
  obtain ⟨z, hz0, hz1⟩ := ((eventually_nhdsWithin_of_eventually_nhds hev).and
    (ZerosCountable.isolated_zero_riemannZeta hρ1)).exists
  exact hz1 hz0

/-- The order of vanishing of `ζ` at `ρ`, as a natural number (`analyticOrderAt`, which is
finite since `ζ` is not identically zero near `ρ`); `0` by convention at `ρ = 1`. -/
def zetaOrder (ρ : ℂ) : ℕ :=
  if h : ρ = 1 then 0 else (analyticOrderAt riemannZeta ρ).toNat

/-- **Local factorisation.** At `ρ ≠ 1`: `ζ z = (z − ρ)^{zetaOrder ρ} · g z` near `ρ`, with `g`
analytic at `ρ` and `g ρ ≠ 0`. -/
theorem exists_factorization {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ z in 𝓝 ρ, riemannZeta z = (z - ρ) ^ zetaOrder ρ * g z := by
  have han : AnalyticAt ℂ riemannZeta ρ := analyticAt_riemannZeta_of_ne_one hρ1
  have hne : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
    fun h => not_eventually_zero hρ1 (analyticOrderAt_eq_top.mp h)
  obtain ⟨g, hg, hg0, hfg⟩ := han.analyticOrderAt_ne_top.mp hne
  refine ⟨g, hg, hg0, ?_⟩
  have hord : zetaOrder ρ = analyticOrderNatAt riemannZeta ρ := by
    unfold zetaOrder
    rw [dif_neg hρ1]
    rfl
  rw [hord]
  filter_upwards [hfg] with z hz
  simp only [smul_eq_mul] at hz ⊢
  exact hz

/-- At a zero `ρ ≠ 1` of `ζ`, the order of vanishing is positive. -/
theorem zetaOrder_pos {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ0 : riemannZeta ρ = 0) : 0 < zetaOrder ρ := by
  obtain ⟨g, -, hg0, hfg⟩ := exists_factorization hρ1
  rcases Nat.eq_zero_or_pos (zetaOrder ρ) with h0 | hpos
  · exfalso
    have h := hfg.self_of_nhds
    rw [hρ0, h0, sub_self, pow_zero, one_mul] at h
    exact hg0 h.symm
  · exact hpos

/-! ## Logarithmic derivatives near a zero of finite order -/

/-- If `f = (· − p)^n · g` near `p` with `g` analytic at `p` and `g p ≠ 0`, then
`f'/f = n/(z − p) + g'/g` on a punctured neighbourhood of `p`. -/
theorem logDeriv_eventually_eq_of_eventually_eq_pow_mul {f g : ℂ → ℂ} {p : ℂ}
    (hg : AnalyticAt ℂ g p) (hg0 : g p ≠ 0) (n : ℕ)
    (hf : ∀ᶠ z in 𝓝 p, f z = (z - p) ^ n * g z) :
    ∀ᶠ z in 𝓝[≠] p, deriv f z / f z = (n : ℂ) / (z - p) + deriv g z / g z := by
  have hg_ne : ∀ᶠ z in 𝓝 p, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hderiv := LogDerivResidue.deriv_eq_of_eventually_eq_pow_mul hg n hf
  have hall : ∀ᶠ z in 𝓝 p, f z = (z - p) ^ n * g z ∧ g z ≠ 0 ∧
      deriv f z = (n : ℂ) * (z - p) ^ (n - 1) * g z + (z - p) ^ n * deriv g z :=
    hf.and (hg_ne.and hderiv)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hall, self_mem_nhdsWithin]
    with z ⟨hfz, hgz, hdz⟩ hzp
  have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
  rw [hfz, hdz]
  rcases n with _ | k
  · simp
  · have hk : (k + 1 : ℕ) - 1 = k := by omega
    rw [hk]
    push_cast
    field_simp
    ring

/-- **Removing one principal part.** If `f'/f = coef p/(z − p) + g'/g` near `p` (punctured),
with `g` analytic at `p`, `g p ≠ 0`, and `p ∈ P`, then `f'/f − ∑ q ∈ P, coef q/(z − q)` tends to
`g'(p)/g(p) − ∑ q ∈ P.erase p, coef q/(p − q)` as `z → p`, `z ≠ p`. -/
theorem tendsto_sub_principalPart {f g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p) (hg0 : g p ≠ 0)
    (P : Finset ℂ) (coef : ℂ → ℂ) (hp : p ∈ P)
    (hf : ∀ᶠ z in 𝓝[≠] p, deriv f z / f z = coef p / (z - p) + deriv g z / g z) :
    Tendsto (fun s => deriv f s / f s - ∑ q ∈ P, coef q / (s - q)) (𝓝[≠] p)
      (𝓝 (deriv g p / g p - ∑ q ∈ P.erase p, coef q / (p - q))) := by
  have hcont : ContinuousAt (fun s => deriv g s / g s - ∑ q ∈ P.erase p, coef q / (s - q)) p := by
    have h1 : ContinuousAt (fun s => deriv g s / g s) p :=
      (LogDerivResidue.continuousAt_deriv_of_analyticAt hg).div hg.continuousAt hg0
    have h2 : DifferentiableAt ℂ (fun s => ∑ q ∈ P.erase p, coef q / (s - q)) p := by
      apply DifferentiableAt.fun_sum
      intro q hq
      have hqp : p - q ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hq).symm
      exact (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) hqp
    exact h1.sub h2.continuousAt
  refine (tendsto_nhdsWithin_of_tendsto_nhds hcont.tendsto).congr' ?_
  filter_upwards [hf, self_mem_nhdsWithin] with s hs _
  rw [hs, ← Finset.add_sum_erase P _ hp]
  ring

/-! ## The gluing lemma: removable singularities at finitely many punctures -/

/-- On a punctured neighbourhood of `p`, points avoid the finite set `P`. -/
theorem eventually_not_mem_punctured (P : Finset ℂ) (p : ℂ) : ∀ᶠ t in 𝓝[≠] p, t ∉ P := by
  have hopen : IsOpen ((↑(P.erase p) : Set ℂ)ᶜ) :=
    (P.erase p).finite_toSet.isClosed.isOpen_compl
  have hp : p ∈ ((↑(P.erase p) : Set ℂ)ᶜ) :=
    Set.mem_compl (fun h => Finset.notMem_erase p P (Finset.mem_coe.mp h))
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds hp),
    self_mem_nhdsWithin] with t ht htp htP
  exact ht (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨htp, htP⟩))

/-- **Gluing lemma.** Let `P` be a finite set of punctures and `H₀` a function which is complex
differentiable at every point of `K` off `P`, differentiable on a punctured neighbourhood of
each puncture, and has a limit at each puncture. Then there is `H`, agreeing with `H₀` off `P`,
which is complex differentiable at every point of `K`. -/
theorem exists_differentiableAt_of_tendsto_punctures (K : Set ℂ) (P : Finset ℂ) (H₀ : ℂ → ℂ)
    (hdiff : ∀ s ∈ K, s ∉ P → DifferentiableAt ℂ H₀ s)
    (hdiff' : ∀ p ∈ P, ∀ᶠ t in 𝓝[≠] p, DifferentiableAt ℂ H₀ t)
    (hlim : ∀ p ∈ P, ∃ L : ℂ, Tendsto H₀ (𝓝[≠] p) (𝓝 L)) :
    ∃ H : ℂ → ℂ, (∀ s ∈ K, DifferentiableAt ℂ H s) ∧ ∀ s, s ∉ P → H s = H₀ s := by
  have hlim' : ∀ p : ℂ, ∃ L : ℂ, p ∈ P → Tendsto H₀ (𝓝[≠] p) (𝓝 L) := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨L, hL⟩ := hlim p hp
      exact ⟨L, fun _ => hL⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose L hL using hlim'
  obtain ⟨H, hHdef⟩ : ∃ H : ℂ → ℂ, H = fun s => if s ∈ P then L s else H₀ s := ⟨_, rfl⟩
  have hH_not : ∀ s, s ∉ P → H s = H₀ s := by
    intro s hs
    rw [hHdef]
    exact if_neg hs
  have hH_mem : ∀ s ∈ P, H s = L s := by
    intro s hs
    rw [hHdef]
    exact if_pos hs
  have hPc : IsOpen ((↑P : Set ℂ)ᶜ) := P.finite_toSet.isClosed.isOpen_compl
  have hev_not : ∀ s, s ∉ P → H =ᶠ[𝓝 s] H₀ := by
    intro s hs
    filter_upwards [hPc.mem_nhds (Set.mem_compl fun h => hs (Finset.mem_coe.mp h))] with t ht
    exact hH_not t ht
  refine ⟨H, ?_, hH_not⟩
  intro s hsK
  by_cases hsP : s ∈ P
  · -- a puncture: differentiable on a punctured neighbourhood, continuous at `s`
    have hV : {t : ℂ | t ≠ s → DifferentiableAt ℂ H₀ t ∧ t ∉ P} ∈ 𝓝 s := by
      have h : ∀ᶠ t in 𝓝 s, t ≠ s → DifferentiableAt ℂ H₀ t ∧ t ∉ P :=
        eventually_nhdsWithin_iff.mp ((hdiff' s hsP).and (eventually_not_mem_punctured P s))
      exact h
    have hV_diff : DifferentiableOn ℂ H
        ({t : ℂ | t ≠ s → DifferentiableAt ℂ H₀ t ∧ t ∉ P} \ {s}) := by
      intro t ht
      have hts : t ≠ s := ht.2
      obtain ⟨hd, htP⟩ := ht.1 hts
      exact (hd.congr_of_eventuallyEq (hev_not t htP)).differentiableWithinAt
    have hcont : ContinuousAt H s := by
      rw [← continuousWithinAt_compl_self]
      show Tendsto H (𝓝[≠] s) (𝓝 (H s))
      rw [hH_mem s hsP]
      refine (hL s hsP).congr' ?_
      filter_upwards [eventually_not_mem_punctured P s] with t ht
      exact (hH_not t ht).symm
    exact ((Complex.differentiableOn_compl_singleton_and_continuousAt_iff hV).mp
      ⟨hV_diff, hcont⟩).differentiableAt hV
  · exact (hdiff s hsK hsP).congr_of_eventuallyEq (hev_not s hsP)

/-! ## The principal part of `ζ'/ζ` on the rectangle -/

/-- The residue of `ζ'/ζ` at a puncture: `−1` at the pole `1`, the order `zetaOrder q` at a
zero `q`. -/
def coef (q : ℂ) : ℂ := if q = 1 then -1 else (zetaOrder q : ℂ)

/-- `coef 1 = −1`. -/
theorem coef_one : coef 1 = -1 := if_pos rfl

/-- `coef q = zetaOrder q` for `q ≠ 1`. -/
theorem coef_of_ne_one {q : ℂ} (hq : q ≠ 1) : coef q = (zetaOrder q : ℂ) := if_neg hq

/-- The puncture set of `ζ'/ζ` in the rectangle: the pole `1` and the zeros. -/
def punctures (c T : ℝ) : Finset ℂ := insert (1 : ℂ) (zeroFinset c T)

/-- Membership in `punctures`. -/
theorem mem_punctures {c T : ℝ} {q : ℂ} : q ∈ punctures c T ↔ q = 1 ∨ q ∈ zeroFinset c T :=
  Finset.mem_insert

/-- `1 ∈ punctures c T`. -/
theorem one_mem_punctures (c T : ℝ) : (1 : ℂ) ∈ punctures c T := Finset.mem_insert_self _ _

/-- The principal part over the punctures, written out:
`∑ q ∈ punctures, coef q/(s − q) = −1/(s − 1) + ∑ ρ ∈ zeroFinset, zetaOrder ρ/(s − ρ)`. -/
theorem sum_coef_punctures (c T : ℝ) (s : ℂ) :
    ∑ q ∈ punctures c T, coef q / (s - q) =
      -1 / (s - 1) + ∑ ρ ∈ zeroFinset c T, (zetaOrder ρ : ℂ) / (s - ρ) := by
  unfold punctures
  rw [Finset.sum_insert (one_not_mem_zeroFinset c T), coef_one]
  congr 1
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [coef_of_ne_one (mem_zeroFinset.mp hρ).2.1]

/-- The naive remainder `ζ'/ζ − ∑ q ∈ punctures, coef q/(s − q)` (junk values at the
punctures, where Lean's `x / 0 = 0` convention applies). -/
def naiveRemainder (c T : ℝ) : ℂ → ℂ :=
  fun s => deriv riemannZeta s / riemannZeta s - ∑ q ∈ punctures c T, coef q / (s - q)

/-- The naive remainder is complex differentiable at every non-puncture where `ζ ≠ 0`. -/
theorem naiveRemainder_differentiableAt (c T : ℝ) {s : ℂ} (hsP : s ∉ punctures c T)
    (hs0 : riemannZeta s ≠ 0) : DifferentiableAt ℂ (naiveRemainder c T) s := by
  have hs1 : s ≠ 1 := fun h => hsP (by rw [h]; exact one_mem_punctures c T)
  have hζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hζ' : DifferentiableAt ℂ (deriv riemannZeta) s :=
    (ZerosCountable.analyticOnNhd_riemannZeta.deriv s
      (Set.mem_compl_singleton_iff.mpr hs1)).differentiableAt
  unfold naiveRemainder
  refine (hζ'.div hζ hs0).sub (DifferentiableAt.fun_sum fun q hq => ?_)
  have hsq : s - q ≠ 0 := sub_ne_zero.mpr (fun h => hsP (by rw [h]; exact hq))
  exact (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) hsq

/-- The naive remainder is complex differentiable on a punctured neighbourhood of every point. -/
theorem eventually_differentiableAt_naiveRemainder (c T : ℝ) (p : ℂ) :
    ∀ᶠ t in 𝓝[≠] p, DifferentiableAt ℂ (naiveRemainder c T) t := by
  filter_upwards [eventually_not_mem_punctured (punctures c T) p, eventually_ne_zero_punctured p]
    with t htP ht0
  exact naiveRemainder_differentiableAt c T htP ht0

/-- **The naive remainder has a limit at every puncture** (the principal part has been
subtracted off: at a zero via the local factorisation, at `1` via `zetaNum`). -/
theorem exists_tendsto_naiveRemainder (c T : ℝ) {p : ℂ} (hp : p ∈ punctures c T) :
    ∃ L : ℂ, Tendsto (naiveRemainder c T) (𝓝[≠] p) (𝓝 L) := by
  rcases mem_punctures.mp hp with rfl | hpZ
  · -- the pole `1`
    refine ⟨_, tendsto_sub_principalPart (differentiable_zetaNum.analyticAt 1)
      (by rw [zetaNum_one]; exact one_ne_zero) (punctures c T) coef hp ?_⟩
    filter_upwards [logDeriv_zeta_eventually_eq_near_one] with s hs
    rw [hs, coef_one]
  · -- a zero
    obtain ⟨-, hp1, -⟩ := mem_zeroFinset.mp hpZ
    obtain ⟨g, hg, hg0, hfg⟩ := exists_factorization hp1
    refine ⟨_, tendsto_sub_principalPart hg hg0 (punctures c T) coef hp ?_⟩
    filter_upwards [logDeriv_eventually_eq_of_eventually_eq_pow_mul hg hg0 (zetaOrder p) hfg]
      with s hs
    rw [hs, coef_of_ne_one hp1]

/-! ## The holomorphic remainder -/

/-- **Existence of the holomorphic remainder (explicit `Z`, `m`).** There is `H`, complex
differentiable at every point of the closed rectangle, with
`ζ'/ζ (s) = H s + ∑ ρ ∈ zeroFinset c T, zetaOrder ρ/(s − ρ) − 1/(s − 1)`
at every `s` of the closed rectangle with `ζ s ≠ 0`, `s ≠ 1`. -/
theorem exists_remainder_differentiableAt (c T : ℝ) :
    ∃ H : ℂ → ℂ, (∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], DifferentiableAt ℂ H s) ∧
      ∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], riemannZeta s ≠ 0 → s ≠ 1 →
        deriv riemannZeta s / riemannZeta s =
          H s + ∑ ρ ∈ zeroFinset c T, (zetaOrder ρ : ℂ) / (s - ρ) - 1 / (s - 1) := by
  obtain ⟨H, hHd, hHeq⟩ := exists_differentiableAt_of_tendsto_punctures
    ([[1 - c, c]] ×ℂ [[-T, T]]) (punctures c T) (naiveRemainder c T)
    (fun s hs hsP => by
      refine naiveRemainder_differentiableAt c T hsP ?_
      intro hs0
      have hs1 : s ≠ 1 := fun h => hsP (by rw [h]; exact one_mem_punctures c T)
      exact hsP (mem_punctures.mpr (Or.inr (mem_zeroFinset.mpr ⟨hs, hs1, hs0⟩))))
    (fun p _ => eventually_differentiableAt_naiveRemainder c T p)
    (fun p hp => exists_tendsto_naiveRemainder c T hp)
  refine ⟨H, hHd, fun s _ hs0 hs1 => ?_⟩
  have hsP : s ∉ punctures c T := by
    intro h
    rcases mem_punctures.mp h with h1 | hZ
    · exact hs1 h1
    · exact hs0 (mem_zeroFinset.mp hZ).2.2
  rw [hHeq s hsP]
  unfold naiveRemainder
  rw [sum_coef_punctures]
  ring

/-- **The principal-part hypothesis `hH` of `ContourShift.contour_shift_rectangle`, discharged.**
For `c > 1`, `T > 0` there are a finite set `Z` (the zeros of `ζ` in the closed rectangle other
than `1`), multiplicities `m` (the orders of vanishing), and a holomorphic `H` on the closed
rectangle with `ζ'/ζ (s) = H s + ∑ ρ ∈ Z, m ρ/(s − ρ) − 1/(s − 1)` wherever `ζ s ≠ 0`, `s ≠ 1`.
`Z` is characterised by the first two clauses and `1 ∉ Z`. -/
theorem exists_holomorphic_remainder (c T : ℝ) (_hc : 1 < c) (_hT : 0 < T) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ Z, ρ ∈ [[1 - c, c]] ×ℂ [[-T, T]] ∧ ρ ≠ 1 ∧ riemannZeta ρ = 0) ∧
      (∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], s ≠ 1 → riemannZeta s = 0 → s ∈ Z) ∧
      (1 : ℂ) ∉ Z ∧
      ∃ H : ℂ → ℂ, DifferentiableOn ℂ H ([[1 - c, c]] ×ℂ [[-T, T]]) ∧
        ∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], riemannZeta s ≠ 0 → s ≠ 1 →
          deriv riemannZeta s / riemannZeta s =
            H s + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) - 1 / (s - 1) := by
  obtain ⟨H, hHd, hHeq⟩ := exists_remainder_differentiableAt c T
  exact ⟨zeroFinset c T, zetaOrder, fun ρ hρ => mem_zeroFinset.mp hρ,
    fun s hs hs1 hs0 => mem_zeroFinset.mpr ⟨hs, hs1, hs0⟩, one_not_mem_zeroFinset c T,
    H, fun s hs => (hHd s hs).differentiableWithinAt, hHeq⟩

/-- The multiplicities in `exists_holomorphic_remainder` are positive: every `ρ ∈ zeroFinset`
has `0 < zetaOrder ρ`. -/
theorem zetaOrder_pos_of_mem_zeroFinset {c T : ℝ} {ρ : ℂ} (hρ : ρ ∈ zeroFinset c T) :
    0 < zetaOrder ρ :=
  zetaOrder_pos (mem_zeroFinset.mp hρ).2.1 (mem_zeroFinset.mp hρ).2.2

/-! ## The contour-shift identity with the analytic input discharged -/

/-- **Contour-shift identity.** For `c > 1`, `T > 0`, `G` holomorphic on the closed rectangle
`[[1 − c, c]] ×ℂ [[−T, T]]`, `F G = (ζ'/ζ) · G` segment integrable on its boundary, and no zero of
`ζ` on the boundary of the rectangle (`hbd`, which also covers the trivial zeros on the left
edge when `c − 1 ∈ 2ℕ`), the boundary integral of `F G` equals
`2πI · (∑ ρ ∈ zeroFinset c T, zetaOrder ρ · G ρ − G 1)`.
Compared with `ContourShift.contour_shift_rectangle`, the hypotheses `hZ_in`, `hZ_one`, `hZ_all`
and `hH` are discharged; `hbd` is the only new input (it is not implied by `hF`). -/
theorem contour_shift_rectangle_of_G (c T : ℝ) (hc : 1 < c) (hT : 0 < T) (G : ℂ → ℂ)
    (hG : DifferentiableOn ℂ G ([[1 - c, c]] ×ℂ [[-T, T]]))
    (hF : Residue.SegmentIntegrable (ContourShift.F G) ((1 - c) - T * I) (c + T * I))
    (hbd : ∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], s ≠ 1 → riemannZeta s = 0 →
      1 - c < s.re ∧ s.re < c ∧ -T < s.im ∧ s.im < T) :
    Residue.rectBoundaryIntegral (ContourShift.F G) ((1 - c) - T * I) (c + T * I) =
      2 * π * I * (∑ ρ ∈ zeroFinset c T, (zetaOrder ρ : ℂ) * G ρ - G 1) := by
  obtain ⟨H, hHd, hHeq⟩ := exists_remainder_differentiableAt c T
  refine ContourShift.contour_shift_rectangle c T hc hT G (zeroFinset c T) zetaOrder hG ?_
    (one_not_mem_zeroFinset c T) (fun s hs hs1 hs0 => mem_zeroFinset.mpr ⟨hs, hs1, hs0⟩)
    ⟨H, fun s hs => (hHd s hs).differentiableWithinAt, hHeq⟩ hF
  intro ρ hρ
  obtain ⟨hρR, hρ1, hρ0⟩ := mem_zeroFinset.mp hρ
  exact hbd ρ hρR hρ1 hρ0

/-- **Vertical-line difference** with the analytic input discharged (same hypotheses as
`contour_shift_rectangle_of_G`). -/
theorem vertical_lines_difference_of_G (c T : ℝ) (hc : 1 < c) (hT : 0 < T) (G : ℂ → ℂ)
    (hG : DifferentiableOn ℂ G ([[1 - c, c]] ×ℂ [[-T, T]]))
    (hF : Residue.SegmentIntegrable (ContourShift.F G) ((1 - c) - T * I) (c + T * I))
    (hbd : ∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], s ≠ 1 → riemannZeta s = 0 →
      1 - c < s.re ∧ s.re < c ∧ -T < s.im ∧ s.im < T) :
    I * (∫ y in (-T)..T, ContourShift.F G (c + y * I)) -
        I * (∫ y in (-T)..T, ContourShift.F G ((1 - c) + y * I)) =
      2 * π * I * (∑ ρ ∈ zeroFinset c T, (zetaOrder ρ : ℂ) * G ρ - G 1)
        - (∫ x in (1 - c)..c, ContourShift.F G (x - T * I))
        + (∫ x in (1 - c)..c, ContourShift.F G (x + T * I)) := by
  obtain ⟨H, hHd, hHeq⟩ := exists_remainder_differentiableAt c T
  refine ContourShift.vertical_lines_difference c T hc hT G (zeroFinset c T) zetaOrder hG ?_
    (one_not_mem_zeroFinset c T) (fun s hs hs1 hs0 => mem_zeroFinset.mpr ⟨hs, hs1, hs0⟩)
    ⟨H, fun s hs => (hHd s hs).differentiableWithinAt, hHeq⟩ hF
  intro ρ hρ
  obtain ⟨hρR, hρ1, hρ0⟩ := mem_zeroFinset.mp hρ
  exact hbd ρ hρR hρ1 hρ0

end PrincipalPartDischarge

end
