import FleetWeilPositivity
import OffLineDetection

/-!
# Weil criterion, part 4a: weighted Gaussian detection of an off-line point

A generic version of the dominant-term argument of `FleetHeatPositivityRH`, for an arbitrary
family `τ : ι → ℂ` in the strip `|Im| < 1/2` (finitely many points near any height, tempered)
and a bounded weight `W`:

* `exists_dominant` — if some `τ i₀` is off the real line, there are a centre `α`, a point `p`
  with `Im p ≠ 0` and phase `θ = thetaE α p ≠ 0`, and a nonempty finite set `S` of indices with
  `τ i ∈ {p, conj p}` on `S`, on which the Gaussian exponent `vE α` takes its maximal value
  `M > 0` over the points near `α`, with a gap `ε > 0` to the others. This step does not see `W`.
* `false_of_dominant` — for such data, no weight `W` with `W p ≠ 0`, `W (conj p) = conj (W p)`
  can satisfy the lower bound `Re ∑ᵢ W(τ i) · gaussHat b α (τ i) ≥ −K √(π/b)` for all `b ∈ (0, 1]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Topology Set MeasureTheory
open scoped Real ComplexConjugate

namespace FleetWeilCriterion

namespace OffLine

open OffLineDetection (vE thetaE gaussHat_polar norm_gaussHat_s far_exponent_le tendsto_bound)
open GaussianTest (gaussHat gaussHat_eq norm_gaussHat)

variable {ι : Type*}

/-- A family of points in the strip `|Im| < 1/2`, finitely many near any height, tempered. -/
structure Strip (τ : ι → ℂ) : Prop where
  im_sq : ∀ i, (τ i).im ^ 2 < 1 / 4
  finite : ∀ α : ℝ, {i | |(τ i).re - α| < 1}.Finite
  summable : Summable (fun i => 1 / (1 + (τ i).re ^ 2))

variable {τ : ι → ℂ}

/-- The points near `α`. -/
def Zs (τ : ι → ℂ) (α : ℝ) : Set ι := {i | |(τ i).re - α| < 1}

/-- The points near `α`, as a finset. -/
def Zsf (h : Strip τ) (α : ℝ) : Finset ι := (h.finite α).toFinset

lemma mem_Zsf {h : Strip τ} {α : ℝ} {i : ι} : i ∈ Zsf h α ↔ |(τ i).re - α| < 1 := by
  simp [Zsf]

/-- Far weights. -/
def ws (τ : ι → ℂ) (α : ℝ) (i : ι) : ℝ := Real.exp (-((τ i).re - α) ^ 2 / 4)

lemma ws_nonneg (α : ℝ) (i : ι) : 0 ≤ ws τ α i := by unfold ws; positivity

lemma summable_ws (h : Strip τ) (α : ℝ) : Summable (ws τ α) := by
  obtain ⟨C, hC⟩ := RealSideBound.gaussian_le_inv_sq α
  refine Summable.of_nonneg_of_le (ws_nonneg α) (fun i => ?_) (h.summable.mul_left C)
  unfold ws
  calc Real.exp (-((τ i).re - α) ^ 2 / 4) ≤ C / (1 + (τ i).re ^ 2) := hC _
    _ = C * (1 / (1 + (τ i).re ^ 2)) := by ring

lemma norm_gH_far (h : Strip τ) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {α : ℝ} {i : ι}
    (hi : i ∉ Zs τ α) :
    ‖gaussHat b α (τ i)‖ ≤ Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) *
      (Real.exp (1 / 4) * ws τ α i) := by
  have hre : 1 ≤ |(τ i).re - α| := not_lt.mp hi
  rw [norm_gaussHat hb]
  have hf := far_exponent_le hb hb1 (h.im_sq i) hre
  calc Real.sqrt (π / b) * Real.exp (((τ i).im ^ 2 - ((τ i).re - α) ^ 2) / (4 * b))
      ≤ Real.sqrt (π / b) * Real.exp (-3 / (16 * b) + 1 / 4 - ((τ i).re - α) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hf) (Real.sqrt_nonneg _)
    _ = Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * (Real.exp (1 / 4) * ws τ α i) := by
        unfold ws
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, neg_div]
        ring_nf

/-- Global bound `‖gaussHat b α (τ i)‖ ≤ √(π/b) e^{1/(16b)} ws`. -/
lemma norm_gH_le (h : Strip τ) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α : ℝ) (i : ι) :
    ‖gaussHat b α (τ i)‖ ≤ Real.sqrt (π / b) * Real.exp (1 / (16 * b)) * ws τ α i := by
  rw [norm_gaussHat hb, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  unfold ws
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have him := h.im_sq i
  have hX : 0 ≤ ((τ i).re - α) ^ 2 := sq_nonneg _
  have h1 : (τ i).im ^ 2 / (4 * b) ≤ 1 / (16 * b) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : ((τ i).re - α) ^ 2 / 4 ≤ ((τ i).re - α) ^ 2 / (4 * b) := by
    apply div_le_div_of_nonneg_left hX (by positivity); nlinarith
  have : ((τ i).im ^ 2 - ((τ i).re - α) ^ 2) / (4 * b) =
      (τ i).im ^ 2 / (4 * b) - ((τ i).re - α) ^ 2 / (4 * b) := by ring
  rw [this]
  have : -((τ i).re - α) ^ 2 / 4 = -(((τ i).re - α) ^ 2 / 4) := by ring
  rw [this]
  linarith

lemma summable_weighted (h : Strip τ) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α : ℝ)
    (W : ι → ℂ) {CW : ℝ} (hW : ∀ i, ‖W i‖ ≤ CW) :
    Summable (fun i => W i * gaussHat b α (τ i)) := by
  refine Summable.of_norm_bounded
    (((summable_ws h α).mul_left (CW * (Real.sqrt (π / b) * Real.exp (1 / (16 * b)))))) (fun i => ?_)
  rw [norm_mul]
  have h0 : 0 ≤ CW := (norm_nonneg _).trans (hW i)
  calc ‖W i‖ * ‖gaussHat b α (τ i)‖ ≤ CW * (Real.sqrt (π / b) * Real.exp (1 / (16 * b)) * ws τ α i) :=
        mul_le_mul (hW i) (norm_gH_le h hb hb1 α i) (norm_nonneg _) h0
    _ = _ := by ring

theorem tail_bound (h : Strip τ) (α : ℝ) (W : ι → ℂ) {CW : ℝ} (hCW : 0 ≤ CW)
    (hW : ∀ i, ‖W i‖ ≤ CW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' i, (Zs τ α)ᶜ.indicator (fun i => W i * gaussHat b α (τ i)) i‖
        ≤ Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * C := by
  refine ⟨CW * (Real.exp (1 / 4) * ∑' i, ws τ α i),
    mul_nonneg hCW (mul_nonneg (Real.exp_pos _).le (tsum_nonneg (ws_nonneg α))), fun b hb hb1 => ?_⟩
  have hsw : Summable (fun i => CW * (Real.exp (1 / 4) * ws τ α i)) :=
    ((summable_ws h α).mul_left _).mul_left _
  have hg : HasSum (fun i => Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) *
      (CW * (Real.exp (1 / 4) * ws τ α i)))
      (Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * (CW * (Real.exp (1 / 4) * ∑' i, ws τ α i))) := by
    have := (hsw.mul_left (Real.sqrt (π / b) * Real.exp (-3 / (16 * b)))).hasSum
    rw [tsum_mul_left, tsum_mul_left, tsum_mul_left] at this
    exact this
  refine tsum_of_norm_bounded hg (fun i => ?_)
  by_cases hi : i ∈ (Zs τ α)ᶜ
  · rw [Set.indicator_of_mem hi, norm_mul]
    calc ‖W i‖ * ‖gaussHat b α (τ i)‖ ≤ CW * (Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) *
          (Real.exp (1 / 4) * ws τ α i)) :=
          mul_le_mul (hW i) (norm_gH_far h hb hb1 hi) (norm_nonneg _) hCW
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hi, norm_zero]
    have := ws_nonneg (τ := τ) α i
    positivity

lemma tsum_split (h : Strip τ) (α : ℝ) (f : ι → ℂ) (hf : Summable f) :
    ∑' i, f i = ∑ i ∈ Zsf h α, f i + ∑' i, (Zs τ α)ᶜ.indicator f i := by
  have h1 : Summable ((Zs τ α).indicator f) := hf.indicator _
  have h2 : Summable ((Zs τ α)ᶜ.indicator f) := hf.indicator _
  have hfin : ∑' i, (Zs τ α).indicator f i = ∑ i ∈ Zsf h α, f i := by
    rw [tsum_eq_sum (s := Zsf h α)]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      exact Set.indicator_of_mem (show i ∈ Zs τ α from mem_Zsf.mp hi) f
    · intro i hi
      exact Set.indicator_of_notMem (show i ∉ Zs τ α from fun h' => hi (mem_Zsf.mpr h')) f
  calc ∑' i, f i = ∑' i, ((Zs τ α).indicator f i + (Zs τ α)ᶜ.indicator f i) := by
        simp only [Set.indicator_self_add_compl_apply]
    _ = ∑' i, (Zs τ α).indicator f i + ∑' i, (Zs τ α)ᶜ.indicator f i := h1.tsum_add h2
    _ = ∑ i ∈ Zsf h α, f i + ∑' i, (Zs τ α)ᶜ.indicator f i := by rw [hfin]

lemma exists_gap (Zf : Finset ι) (v : ι → ℝ) (M : ℝ) (hM : ∀ x ∈ Zf, v x ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Zf, v x ≠ M → v x ≤ M - ε := by
  classical
  set R := Zf.filter (fun x => v x ≠ M) with hR
  by_cases hne : R.Nonempty
  · obtain ⟨xr, hxr, hmax⟩ := Finset.exists_max_image R v hne
    have hxr' := Finset.mem_filter.mp hxr
    have hlt : v xr < M := lt_of_le_of_ne (hM xr hxr'.1) hxr'.2
    refine ⟨M - v xr, by linarith, fun x hx hvx => ?_⟩
    have := hmax x (Finset.mem_filter.mpr ⟨hx, hvx⟩)
    linarith
  · refine ⟨1, one_pos, fun x hx hvx => ?_⟩
    exact absurd ⟨x, Finset.mem_filter.mpr ⟨hx, hvx⟩⟩ hne

lemma vE_conj (α : ℝ) (z : ℂ) : vE α (conj z) = vE α z := by
  simp [vE]

lemma thetaE_conj (α : ℝ) (z : ℂ) : thetaE α (conj z) = -thetaE α z := by
  simp [thetaE]

set_option maxHeartbeats 4000000 in
/-- **The dominant point.** An off-line point yields a centre `α`, a point `p` with nonzero phase,
and a finite dominant set `S ⊆ {p, conj p}` with a gap. -/
theorem exists_dominant (h : Strip τ) {i₀ : ι} (hi₀ : (τ i₀).im ≠ 0) :
    ∃ (α M ε : ℝ) (p : ℂ) (S : Finset ι), 0 < M ∧ 0 < ε ∧ thetaE α p ≠ 0 ∧
      S ⊆ Zsf h α ∧ S.Nonempty ∧ (∀ i ∈ S, τ i = p ∨ τ i = conj p) ∧
      (∀ i ∈ S, vE α (τ i) = M) ∧ (∀ i ∈ Zsf h α, i ∉ S → vE α (τ i) ≤ M - ε) := by
  classical
  set α₀ : ℝ := (τ i₀).re with hα₀
  have hx₀ : i₀ ∈ Zsf h α₀ := by rw [mem_Zsf, hα₀, sub_self, abs_zero]; exact one_pos
  obtain ⟨xm, hxm, hmax⟩ := Finset.exists_max_image (Zsf h α₀) (fun x => vE α₀ (τ x)) ⟨i₀, hx₀⟩
  obtain ⟨M₀, hM₀def⟩ : ∃ M₀ : ℝ, M₀ = vE α₀ (τ xm) := ⟨_, rfl⟩
  rw [← hM₀def] at hmax
  have hM₀ : 0 < M₀ := by
    have h0 : vE α₀ (τ i₀) = (τ i₀).im ^ 2 := by simp only [vE, hα₀, sub_self]; ring
    have h1 : 0 < (τ i₀).im ^ 2 := by positivity
    have := hmax i₀ hx₀; linarith
  set S₀ : Finset ι := (Zsf h α₀).filter (fun x => vE α₀ (τ x) = M₀)
  have hxmS₀ : xm ∈ S₀ := Finset.mem_filter.mpr ⟨hxm, hM₀def.symm⟩
  obtain ⟨ε₀, hε₀, hgap₀⟩ := exists_gap (Zsf h α₀) (fun x => vE α₀ (τ x)) M₀
    (fun x hx => hmax x hx)
  obtain ⟨xd, hxd, hdmax⟩ := Finset.exists_max_image S₀ (fun x => (τ x).re - α₀) ⟨xm, hxmS₀⟩
  obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = (τ xd).re - α₀ := ⟨_, rfl⟩
  rw [← hddef] at hdmax
  set S₁ : Finset ι := S₀.filter (fun x => (τ x).re - α₀ = d)
  have hxdS₁ : xd ∈ S₁ := Finset.mem_filter.mpr ⟨hxd, hddef.symm⟩
  obtain ⟨η, hη, hgapd⟩ := exists_gap S₀ (fun x => (τ x).re - α₀) d (fun x hx => hdmax x hx)
  have hoff : ∀ x ∈ S₀, ((τ x).re - α₀) ^ 2 < 1 / 4 := by
    intro x hx
    have hv : vE α₀ (τ x) = M₀ := (Finset.mem_filter.mp hx).2
    have := h.im_sq x
    simp only [vE] at hv
    linarith
  have hd2 : d ^ 2 < 1 / 4 := by rw [hddef]; exact hoff xd hxd
  have hdabs : |d| < 1 / 2 := by
    rw [← abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    exact sq_lt_sq.mp (by norm_num; linarith)
  obtain ⟨δ₀, hδ₀def⟩ : ∃ δ₀ : ℝ, δ₀ = min (1 / 8) (min (M₀ / 4) (ε₀ / 8)) := ⟨_, rfl⟩
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; exact lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hδ₀8 : δ₀ ≤ 1 / 8 := by rw [hδ₀def]; exact min_le_left _ _
  have hδ₀M : δ₀ ≤ M₀ / 4 := by rw [hδ₀def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ₀ε : δ₀ ≤ ε₀ / 8 := by rw [hδ₀def]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δ, hδpos, hδle, hδne⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ / 2 ∧ δ ≠ d := by
    by_cases hc : δ₀ / 2 = d
    · exact ⟨δ₀ / 3, by positivity, by linarith, fun h' => by rw [← h'] at hc; linarith⟩
    · exact ⟨δ₀ / 2, by positivity, le_rfl, hc⟩
  have hδ8 : δ ≤ 1 / 16 := by linarith
  have hδM : δ ≤ M₀ / 8 := by linarith
  have hδε : δ ≤ ε₀ / 16 := by linarith
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = α₀ + δ := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = M₀ + 2 * δ * d - δ ^ 2 := ⟨_, rfl⟩
  have hdl := abs_lt.mp hdabs
  have hδd : δ * -(1 / 2) ≤ δ * d := mul_le_mul_of_nonneg_left hdl.1.le hδpos.le
  have hδsq : δ ^ 2 ≤ δ / 16 := by nlinarith
  have hMpos : 0 < M := by rw [hMdef]; nlinarith
  have hvshift : ∀ x : ι, vE α (τ x) = vE α₀ (τ x) + 2 * δ * ((τ x).re - α₀) - δ ^ 2 := by
    intro x; simp only [vE]; rw [hαdef]; ring
  have hvS₁ : ∀ x ∈ S₁, vE α (τ x) = M := by
    intro x hx
    have h1 := Finset.mem_filter.mp hx
    have h0 := (Finset.mem_filter.mp h1.1).2
    rw [hvshift, h0, h1.2, hMdef]
  have hS₁sub : S₁ ⊆ Zsf h α := by
    intro x hx
    have h1 := (Finset.mem_filter.mp hx).2
    rw [mem_Zsf]
    have : (τ x).re - α = d - δ := by rw [hαdef]; linarith
    rw [this, abs_lt]; constructor <;> linarith
  have hlt : ∀ x ∈ Zsf h α, x ∉ S₁ → vE α (τ x) < M := by
    intro x hxα hxS₁
    by_cases hx0 : x ∈ Zsf h α₀
    · by_cases hxS₀ : x ∈ S₀
      · have hne : (τ x).re - α₀ ≠ d := fun h' => hxS₁ (Finset.mem_filter.mpr ⟨hxS₀, h'⟩)
        have hle := hgapd x hxS₀ hne
        have h0 := (Finset.mem_filter.mp hxS₀).2
        rw [hvshift, h0, hMdef]
        have := mul_le_mul_of_nonneg_left hle hδpos.le
        nlinarith [mul_pos hδpos hη]
      · have hne : vE α₀ (τ x) ≠ M₀ := fun h' => hxS₀ (Finset.mem_filter.mpr ⟨hx0, h'⟩)
        have hle := hgap₀ x hx0 hne
        have hd1 := abs_lt.mp (mem_Zsf.mp hx0)
        have := mul_le_mul_of_nonneg_left hd1.2.le hδpos.le
        rw [hvshift, hMdef]
        nlinarith
    · have hfar : 1 ≤ |(τ x).re - α₀| := by
        by_contra h'; push Not at h'; exact hx0 (mem_Zsf.mpr h')
      have him := h.im_sq x
      have h3 : (τ x).re - α = ((τ x).re - α₀) - δ := by rw [hαdef]; ring
      have hge : 1 - δ ≤ |(τ x).re - α| := by
        rw [h3]
        have := abs_sub_abs_le_abs_sub ((τ x).re - α₀) δ
        rw [abs_of_pos hδpos] at this; linarith
      have h0 : 0 ≤ 1 - δ := by linarith
      have hsq : (1 - δ) ^ 2 ≤ ((τ x).re - α) ^ 2 := by
        calc (1 - δ) ^ 2 ≤ |(τ x).re - α| ^ 2 := pow_le_pow_left₀ h0 hge 2
          _ = ((τ x).re - α) ^ 2 := sq_abs _
      have h15 : 1 / 4 < (1 - δ) ^ 2 := by
        have h1516 : (15 / 16 : ℝ) ≤ 1 - δ := by linarith
        have := pow_le_pow_left₀ (by norm_num) h1516 2
        linarith
      show (τ x).im ^ 2 - ((τ x).re - α) ^ 2 < M
      linarith
  obtain ⟨ε, hε, hgap⟩ := exists_gap (Zsf h α) (fun x => vE α (τ x)) M
    (fun x hx => by
      by_cases h' : x ∈ S₁
      · exact le_of_eq (hvS₁ x h')
      · exact (hlt x hx h').le)
  have hgap' : ∀ x ∈ Zsf h α, x ∉ S₁ → vE α (τ x) ≤ M - ε := by
    intro x hx hxS
    exact hgap x hx (fun h' => absurd h' (ne_of_lt (hlt x hx hxS)))
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.sqrt (M₀ + d ^ 2) := ⟨_, rfl⟩
  have hE : 0 < E := by rw [hEdef]; exact Real.sqrt_pos.2 (by nlinarith)
  set p : ℂ := ⟨α₀ + d, E⟩
  refine ⟨α, M, ε, p, S₁, hMpos, hε, ?_, hS₁sub, ⟨xd, hxdS₁⟩, ?_, hvS₁, hgap'⟩
  · simp only [thetaE, p]
    have hdδ : (α₀ + d) - α ≠ 0 := by rw [hαdef]; intro h'; apply hδne; linarith
    exact mul_ne_zero (mul_ne_zero (by norm_num) hdδ) hE.ne'
  · intro x hx
    have h1 := Finset.mem_filter.mp hx
    have h0 := (Finset.mem_filter.mp h1.1).2
    have hre : (τ x).re = α₀ + d := by linarith [h1.2]
    have him2 : (τ x).im ^ 2 = E ^ 2 := by
      rw [hEdef, Real.sq_sqrt (by nlinarith)]
      simp only [vE] at h0; rw [h1.2] at h0; linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp him2 with him | him
    · left; apply Complex.ext <;> simp [p, hre, him]
    · right; apply Complex.ext <;> simp [p, hre, him]

/-- Phase selection: for `θ ≠ 0` there are arbitrarily large `s` with `cos (φ + θ s) = −1`. -/
lemma exists_cos_eq_neg_one (φ θ : ℝ) (hθ : θ ≠ 0) (X : ℝ) :
    ∃ s : ℝ, X ≤ s ∧ Real.cos (φ + θ * s) = -1 := by
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · obtain ⟨k, hk⟩ := exists_nat_ge ((X * (-θ) + |φ| + π) / (2 * π))
    have hk' : X * (-θ) + |φ| + π ≤ 2 * π * k := by
      rw [div_le_iff₀ (by positivity)] at hk; linarith
    refine ⟨(2 * π * k + φ - π) / (-θ), ?_, ?_⟩
    · rw [le_div_iff₀ (by linarith)]
      have := neg_abs_le φ
      linarith
    · have : φ + θ * ((2 * π * k + φ - π) / (-θ)) = π - (k : ℕ) * (2 * π) := by
        field_simp; ring
      rw [this, Real.cos_sub_nat_mul_two_pi, Real.cos_pi]
  · obtain ⟨k, hk⟩ := exists_nat_ge ((X * θ + |φ|) / (2 * π))
    have hk' : X * θ + |φ| ≤ 2 * π * k := by
      rw [div_le_iff₀ (by positivity)] at hk; linarith
    refine ⟨(π - φ + 2 * π * k) / θ, ?_, ?_⟩
    · rw [le_div_iff₀ hpos]
      have := le_abs_self φ
      linarith [Real.pi_pos]
    · have : φ + θ * ((π - φ + 2 * π * k) / θ) = π + (k : ℕ) * (2 * π) := by
        field_simp; ring
      rw [this, Real.cos_add_nat_mul_two_pi, Real.cos_pi]

/-- `Re (w · e^{iθs}) = ‖w‖ cos (arg w + θ s)`. -/
lemma re_mul_exp (w : ℂ) (θ s : ℝ) :
    (w * Complex.exp (I * (θ : ℂ) * (s : ℂ))).re = ‖w‖ * Real.cos (Complex.arg w + θ * s) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
  rw [mul_assoc, ← Complex.exp_add]
  have : (Complex.arg w : ℂ) * I + I * (θ : ℂ) * (s : ℂ) = ((Complex.arg w + θ * s : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

set_option maxHeartbeats 4000000 in
/-- **No admissible weight survives a dominant off-line point.** -/
theorem false_of_dominant (h : Strip τ) {α M ε : ℝ} {p : ℂ} {S : Finset ι}
    (hM : 0 < M) (hε : 0 < ε) (hθ : thetaE α p ≠ 0) (hS : S ⊆ Zsf h α) (hSne : S.Nonempty)
    (hSp : ∀ i ∈ S, τ i = p ∨ τ i = conj p) (hSM : ∀ i ∈ S, vE α (τ i) = M)
    (hgap : ∀ i ∈ Zsf h α, i ∉ S → vE α (τ i) ≤ M - ε)
    (W : ℂ → ℂ) (hWp : W p ≠ 0) (hWc : W (conj p) = conj (W p)) {CW : ℝ} (hCW : 0 ≤ CW)
    (hWb : ∀ i, ‖W (τ i)‖ ≤ CW) {K : ℝ}
    (hpos : ∀ b : ℝ, 0 < b → b ≤ 1 →
      -(Real.sqrt (π / b) * K) ≤ (∑' i, W (τ i) * gaussHat b α (τ i)).re) : False := by
  classical
  obtain ⟨C, hC0, hC⟩ := tail_bound h α (fun i => W (τ i)) hCW hWb
  set r : ℝ := ‖W p‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr hWp
  set N : ℝ := ((Zsf h α).card : ℝ)
  have hB := tendsto_bound K (N * CW) C M ε hM hε
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hB.eventually_lt_const hr0)
  obtain ⟨s, hsX, hcos⟩ := exists_cos_eq_neg_one (Complex.arg (W p)) (thetaE α p) hθ (max T (1 / 4))
  have hs4 : 1 / 4 ≤ s := le_trans (le_max_right _ _) hsX
  have hsT : T ≤ s := le_trans (le_max_left _ _) hsX
  set b : ℝ := 1 / (4 * s) with hb_def
  have hs0 : 0 < s := by linarith
  have hb : 0 < b := by positivity
  have hb1 : b ≤ 1 := by
    rw [hb_def, div_le_one (by positivity)]; linarith
  have hsb : s = 1 / (4 * b) := by rw [hb_def]; field_simp
  have h316 : -3 / (16 * b) = -(3 / 4) * s := by rw [hb_def]; field_simp; ring
  have hsqrt : 0 < Real.sqrt (π / b) := Real.sqrt_pos.2 (div_pos Real.pi_pos hb)
  set f : ι → ℂ := fun i => W (τ i) * gaussHat b α (τ i) with hf_def
  have hfS : Summable f := summable_weighted h hb hb1 α (fun i => W (τ i)) hWb
  have hsplit := tsum_split h α f hfS
  set A : ℝ := Real.sqrt (π / b) * Real.exp (M * s) * (-r) with hA
  set Bv : ℝ := CW * (Real.sqrt (π / b) * Real.exp ((M - ε) * s)) with hBv
  have hB0 : 0 ≤ Bv := by rw [hBv]; positivity
  -- dominant terms
  have hdom : ∀ i ∈ S, (f i).re = A := by
    intro i hi
    have hpolar := gaussHat_polar hb α (τ i) hsb
    simp only [hf_def]
    rw [hpolar, hSM i hi]
    rcases hSp i hi with hp | hp
    · rw [hp]
      have : W p * ((Real.sqrt (π / b) : ℂ) * ((Real.exp (M * s) : ℝ) : ℂ) *
          Complex.exp (I * ((thetaE α p : ℝ) : ℂ) * (s : ℂ))) =
          ((Real.sqrt (π / b) * Real.exp (M * s) : ℝ) : ℂ) *
            (W p * Complex.exp (I * ((thetaE α p : ℝ) : ℂ) * (s : ℂ))) := by push_cast; ring
      rw [this, Complex.re_ofReal_mul, re_mul_exp, hcos, hA]
      ring
    · rw [hp, thetaE_conj, hWc]
      have : conj (W p) * ((Real.sqrt (π / b) : ℂ) * ((Real.exp (M * s) : ℝ) : ℂ) *
          Complex.exp (I * ((-thetaE α p : ℝ) : ℂ) * (s : ℂ))) =
          ((Real.sqrt (π / b) * Real.exp (M * s) : ℝ) : ℂ) *
            conj (W p * Complex.exp (I * ((thetaE α p : ℝ) : ℂ) * (s : ℂ))) := by
        rw [map_mul, ← Complex.exp_conj]
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
        push_cast; ring_nf
      rw [this, Complex.re_ofReal_mul, Complex.conj_re, re_mul_exp, hcos, hA]
      ring
  have hrest : ∀ i ∈ Zsf h α, i ∉ S → (f i).re ≤ Bv := by
    intro i hi hiS
    have h1 := Complex.re_le_norm (f i)
    simp only [hf_def] at h1 ⊢
    rw [norm_mul, norm_gaussHat_s hb α (τ i) hsb] at h1
    refine h1.trans ?_
    rw [hBv]
    refine mul_le_mul (hWb i) (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (Real.sqrt_nonneg _)) (by positivity) hCW
    exact mul_le_mul_of_nonneg_right (hgap i hi hiS) hs0.le
  have hnear : (∑ i ∈ Zsf h α, f i).re ≤ (S.card : ℝ) * A + N * Bv := by
    rw [Complex.re_sum]
    have hpt : ∀ i ∈ Zsf h α, (f i).re ≤ if i ∈ S then A else Bv := by
      intro i hi
      split_ifs with hiS
      · exact le_of_eq (hdom i hiS)
      · exact hrest i hi hiS
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hfilt : (Zsf h α).filter (fun x => x ∈ S) = S := by
      ext x; simp only [Finset.mem_filter]; exact ⟨fun h' => h'.2, fun h' => ⟨hS h', h'⟩⟩
    rw [hfilt]
    have : (((Zsf h α).filter (fun x => x ∉ S)).card : ℝ) ≤ N :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    nlinarith
  have htail := hC b hb hb1
  rw [h316] at htail
  have ht : (∑' i, (Zs τ α)ᶜ.indicator f i).re ≤
      Real.sqrt (π / b) * Real.exp (-(3 / 4) * s) * C :=
    (Complex.re_le_norm _).trans htail
  have hp := hpos b hb hb1
  change -(Real.sqrt (π / b) * K) ≤ (∑' i, f i).re at hp
  rw [hsplit, Complex.add_re] at hp
  have hcard : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  -- divide by √(π/b) and by e^{Ms}
  have hkey : (S.card : ℝ) * r * Real.exp (M * s) ≤
      K + N * CW * Real.exp ((M - ε) * s) + C * Real.exp (-(3 / 4) * s) := by
    have : Real.sqrt (π / b) * ((S.card : ℝ) * r * Real.exp (M * s)) ≤
        Real.sqrt (π / b) * (K + N * CW * Real.exp ((M - ε) * s) + C * Real.exp (-(3 / 4) * s)) := by
      have e1 : (S.card : ℝ) * A = -(Real.sqrt (π / b) * ((S.card : ℝ) * r * Real.exp (M * s))) := by
        rw [hA]; ring
      have e2 : N * Bv = Real.sqrt (π / b) * (N * CW * Real.exp ((M - ε) * s)) := by
        rw [hBv]; ring
      nlinarith
    exact le_of_mul_le_mul_left this hsqrt
  have hTs := hT s hsT
  have hexp : 0 < Real.exp (M * s) := Real.exp_pos _
  have e2 : Real.exp (-(ε * s)) * Real.exp (M * s) = Real.exp ((M - ε) * s) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (-((M + 3 / 4) * s)) * Real.exp (M * s) = Real.exp (-(3 / 4) * s) := by
    rw [← Real.exp_add]; congr 1; ring
  have e1 : Real.exp (-(M * s)) * Real.exp (M * s) = 1 := by
    rw [← Real.exp_add]; simp
  have hbound : (K * Real.exp (-(M * s)) + N * CW * Real.exp (-(ε * s)) +
      C * Real.exp (-((M + 3 / 4) * s))) * Real.exp (M * s) =
      K + N * CW * Real.exp ((M - ε) * s) + C * Real.exp (-(3 / 4) * s) := by
    have q1 : K * Real.exp (-(M * s)) * Real.exp (M * s) = K := by rw [mul_assoc, e1, mul_one]
    have q2 : N * CW * Real.exp (-(ε * s)) * Real.exp (M * s) = N * CW * Real.exp ((M - ε) * s) := by
      rw [mul_assoc, e2]
    have q3 : C * Real.exp (-((M + 3 / 4) * s)) * Real.exp (M * s) = C * Real.exp (-(3 / 4) * s) := by
      rw [mul_assoc, e3]
    rw [add_mul, add_mul, q1, q2, q3]
  have hlt1 : K * Real.exp (-(M * s)) + N * CW * Real.exp (-(ε * s)) +
      C * Real.exp (-((M + 3 / 4) * s)) < r := hTs
  have : (S.card : ℝ) * r * Real.exp (M * s) < r * Real.exp (M * s) := by
    calc (S.card : ℝ) * r * Real.exp (M * s) ≤ _ := hkey
      _ = _ := hbound.symm
      _ < r * Real.exp (M * s) := mul_lt_mul_of_pos_right hlt1 hexp
  nlinarith [mul_pos hr0 hexp]

end OffLine

end FleetWeilCriterion
