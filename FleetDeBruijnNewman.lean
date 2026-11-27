import Mathlib
import QuasiRHWiring

/-!
# de Bruijn's strip contraction for `H_t` and the de Bruijn–Newman constant

Rodgers–Tao normalization: `H_t(z) = ∫_0^∞ e^{t u²} Φ(u) cos(z u) du` (`dbnH Φ t`), and
`Λ = inf {t : H_t has only real zeros}` (`dbnLambda Φ`, an `EReal` infimum). For Rodgers–Tao's
`Φ`, `H_0(z) = (1/8) ξ(1/2 + i z/2)`, so a zero `z` of `H_0` is `ρ = 1/2 + i z/2` and
`Im z = −2 (Re ρ − 1/2)`: a zero strip `|Re ρ − 1/2| ≤ δ` is the strip `|Im z| ≤ 2δ` for `H_0`.

The theorem is proved for every continuous `Φ ≥ 0` on `(0, ∞)` with `∫_0^∞ Φ > 0` and
`e^{a u²} Φ(u)` integrable on `(0, ∞)` for every real `a`, under the hypothesis
`StripApprox D (dbnH Φ 0)`: `H_0` is a uniform-on-discs limit of real polynomials all of whose
zeros satisfy `(Im z)² ≤ D`.

* `shiftAvg_poly_strip`: for a real polynomial `p` with zeros in `(Im z)² ≤ D` and `l > 0`,
  every zero of `(p(z + i l) + p(z − i l))/2` satisfies `(Im z)² ≤ max (D − l²) 0`
  (per-root identity `root_factor_identity`, product over the roots).
* `StripApprox.shift`, `StripApprox.iterate`, `StripApprox.of_limit`: the class is stable
  under the shift average and under uniform-on-discs limits.
* `StripApprox.differentiable`, `StripApprox.zeros`: a member is entire, and if it is not
  identically zero all its zeros lie in the strip (Hurwitz, via isolated zeros and the maximum
  modulus principle applied to `1/p`).
* `shiftAvg_cosT`: on the transform side the shift average is the multiplier `cosh(l u)`;
  `cosh(√(2t/n) u)^n → e^{t u²}` (`cosh_pow_tendsto`) with domination by `e^{t u²}`
  (`cosh_pow_le`), so `n` shift averages of step `√(2t/n)` converge to `H_t` uniformly on discs.
* `deBruijn_strip`: zeros of `H_t` satisfy `(Im z)² ≤ max (D − 2t) 0` for `t > 0`.
* `Λ_le_of_strip`: `Λ ≤ D/2`.
* `quasiRH_xi_strip`: `QuasiRH` (no zeta zeros with `Re s > 7/8`) puts every `z` with
  `1/2 + i z/2` a nontrivial zero in `(Im z)² ≤ (3/4)²`; `Λ_le_nine_thirtyseconds`: strip
  `(3/4)²` for `H_0` gives `Λ ≤ 9/32`, which is above the Platt–Trudgian record `0.2`
  (`nine_thirtyseconds_gt_record`).

Not formalized here: Rodgers–Tao's `Φ` and the identity `H_0(z) = (1/8) ξ(1/2 + i z/2)`; and the
step from "all zeros of `H_0` in the strip" to `StripApprox` (for `ξ` this is the Hadamard
product: the partial products of `H_0(0) ∏ (1 − z²/z_k²)` are real polynomials with the same
zeros).
-/

open Complex Polynomial MeasureTheory Set Filter Topology

noncomputable section

namespace FleetDeBruijnNewman

def StripZeros (D : ℝ) (f : ℂ → ℂ) : Prop := ∀ z, f z = 0 → z.im ^ 2 ≤ D

def IsRealPoly (p : ℂ[X]) : Prop := ∀ z, starRingEnd ℂ (p.eval z) = p.eval (starRingEnd ℂ z)

def shiftAvg (l : ℝ) (F : ℂ → ℂ) : ℂ → ℂ := fun z => (F (z + I * l) + F (z - I * l)) / 2

theorem root_factor_identity (z a : ℂ) (l : ℝ) :
    normSq (z + I * l - a) * normSq (starRingEnd ℂ z - I * l - a)
      - normSq (z - I * l - a) * normSq (starRingEnd ℂ z + I * l - a)
      = 8 * z.im * l * ((z.re - a.re) ^ 2 + z.im ^ 2 + l ^ 2 - a.im ^ 2) := by
  simp only [normSq_apply, sub_re, add_re, sub_im, add_im, mul_re, mul_im, I_re, I_im, ofReal_re,
    ofReal_im, conj_re, conj_im]
  ring

theorem eval_eq_prod (p : ℂ[X]) (s : ℂ) :
    p.eval s = p.leadingCoeff * (p.roots.map (fun a => s - a)).prod := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := p))]
  simp [eval_multiset_prod, Multiset.map_map]

theorem multiset_prod_bounds {ι : Type*} (L R : ι → ℝ) :
    ∀ s : Multiset ι, (∀ a ∈ s, 0 ≤ R a ∧ R a < L a) →
      0 ≤ (s.map R).prod ∧ (s.map R).prod ≤ (s.map L).prod ∧ 0 < (s.map L).prod ∧
        (s ≠ 0 → (s.map R).prod < (s.map L).prod) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro h
    obtain ⟨h1, h2, h3, -⟩ := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    obtain ⟨ha1, ha2⟩ := h a (Multiset.mem_cons_self a s)
    have hLa : 0 < L a := lt_of_le_of_lt ha1 ha2
    simp only [Multiset.map_cons, Multiset.prod_cons]
    refine ⟨mul_nonneg ha1 h1, mul_le_mul ha2.le h2 h1 hLa.le, mul_pos hLa h3, fun _ => ?_⟩
    calc R a * (s.map R).prod ≤ R a * (s.map L).prod := mul_le_mul_of_nonneg_left h2 ha1
      _ < L a * (s.map L).prod := mul_lt_mul_of_pos_right ha2 h3

theorem ne_zero_of_stripZeros {p : ℂ[X]} {D : ℝ} (hz : StripZeros D (fun z => p.eval z)) :
    p ≠ 0 := by
  rintro rfl
  have := hz (I * ((|D| + 1 : ℝ) : ℂ)) (by simp)
  simp at this
  nlinarith [abs_nonneg D, le_abs_self D]

theorem shiftAvg_ne_zero_upper {p : ℂ[X]} (hp : IsRealPoly p) {D l : ℝ} (hl : 0 < l)
    (hz : StripZeros D (fun z => p.eval z)) {z : ℂ} (hy : 0 < z.im) (hD : D < z.im ^ 2 + l ^ 2) :
    p.eval (z + I * l) + p.eval (z - I * l) ≠ 0 := by
  have hp0 := ne_zero_of_stripZeros hz
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
  by_cases hr : p.roots = 0
  · rw [eval_eq_prod p, eval_eq_prod p, hr]
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one]
    intro h
    apply hlc
    linear_combination h / 2
  set c := normSq p.leadingCoeff
  set L : ℂ → ℝ := fun a => normSq (z + I * l - a) * normSq (starRingEnd ℂ z - I * l - a)
  set R : ℂ → ℝ := fun a => normSq (z - I * l - a) * normSq (starRingEnd ℂ z + I * l - a)
  have hprod : ∀ w₁ w₂ : ℂ, normSq (p.eval w₁) * normSq (p.eval w₂) =
      c ^ 2 * (p.roots.map fun a => normSq (w₁ - a) * normSq (w₂ - a)).prod := by
    intro w₁ w₂
    rw [eval_eq_prod p w₁, eval_eq_prod p w₂, map_mul, map_mul, map_multiset_prod,
      map_multiset_prod, Multiset.map_map, Multiset.map_map, Multiset.prod_map_mul]
    simp only [Function.comp_def]
    ring
  have hA : normSq (p.eval (z + I * l)) ^ 2 = c ^ 2 * (p.roots.map L).prod := by
    have h1 : p.eval (starRingEnd ℂ z - I * l) = starRingEnd ℂ (p.eval (z + I * l)) := by
      rw [hp]; congr 1; simp [map_add, map_mul, conj_ofReal]; ring
    rw [sq, ← hprod]
    · rw [h1, normSq_conj]
  have hB : normSq (p.eval (z - I * l)) ^ 2 = c ^ 2 * (p.roots.map R).prod := by
    have h1 : p.eval (starRingEnd ℂ z + I * l) = starRingEnd ℂ (p.eval (z - I * l)) := by
      rw [hp]; congr 1; simp [map_sub, map_mul, conj_ofReal]
    rw [sq, ← hprod]
    · rw [h1, normSq_conj]
  have hroot : ∀ a ∈ p.roots, 0 ≤ R a ∧ R a < L a := by
    intro a ha
    have haD : a.im ^ 2 ≤ D := hz a ((mem_roots hp0).1 ha)
    refine ⟨mul_nonneg (normSq_nonneg _) (normSq_nonneg _), ?_⟩
    have := root_factor_identity z a l
    have hpos : 0 < 8 * z.im * l * ((z.re - a.re) ^ 2 + z.im ^ 2 + l ^ 2 - a.im ^ 2) := by
      have : 0 < (z.re - a.re) ^ 2 + z.im ^ 2 + l ^ 2 - a.im ^ 2 := by nlinarith [sq_nonneg (z.re - a.re)]
      positivity
    simp only [L, R]; linarith
  obtain ⟨-, -, -, hlt⟩ := multiset_prod_bounds L R p.roots hroot
  have hc : 0 < c ^ 2 := by have := normSq_pos.2 hlc; positivity
  have hsq : normSq (p.eval (z - I * l)) ^ 2 < normSq (p.eval (z + I * l)) ^ 2 := by
    rw [hA, hB]; exact mul_lt_mul_of_pos_left (hlt hr) hc
  have hlt2 : normSq (p.eval (z - I * l)) < normSq (p.eval (z + I * l)) :=
    lt_of_pow_lt_pow_left₀ 2 (normSq_nonneg _) hsq
  intro h
  have : p.eval (z + I * l) = -p.eval (z - I * l) := by linear_combination h
  rw [this, normSq_neg] at hlt2
  exact lt_irrefl _ hlt2

theorem shiftAvg_poly_strip {p : ℂ[X]} (hp : IsRealPoly p) {D l : ℝ} (hl : 0 < l)
    (hz : StripZeros D (fun z => p.eval z)) :
    StripZeros (max (D - l ^ 2) 0) (shiftAvg l fun z => p.eval z) := by
  intro z hz0
  by_contra hlt
  push Not at hlt
  have hD : D < z.im ^ 2 + l ^ 2 := by linarith [le_max_left (D - l ^ 2) 0]
  have hy : z.im ≠ 0 := by
    intro h; rw [h] at hlt; simp at hlt
  have hsum : p.eval (z + I * l) + p.eval (z - I * l) = 0 := by
    simp only [shiftAvg] at hz0; linear_combination 2 * hz0
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · set w := starRingEnd ℂ z
    have hw : 0 < w.im := by simp [w]; linarith
    have hwD : D < w.im ^ 2 + l ^ 2 := by simpa [w] using hD
    apply shiftAvg_ne_zero_upper hp hl hz hw hwD
    have e1 : p.eval (w + I * l) = starRingEnd ℂ (p.eval (z - I * l)) := by
      rw [hp]; congr 1; simp [w, map_sub, map_mul, conj_ofReal]
    have e2 : p.eval (w - I * l) = starRingEnd ℂ (p.eval (z + I * l)) := by
      rw [hp]; congr 1; simp [w, map_add, map_mul, conj_ofReal]; ring
    rw [e1, e2, ← map_add, add_comm, hsum, map_zero]
  · exact shiftAvg_ne_zero_upper hp hl hz hpos hD hsum


/-- `F` is approximable, uniformly on every disc, by real polynomials whose zeros all satisfy
`(Im z)^2 ≤ D`. -/
def StripApprox (D : ℝ) (F : ℂ → ℂ) : Prop :=
  ∀ R ε : ℝ, 0 < ε → ∃ p : ℂ[X], IsRealPoly p ∧ StripZeros D (fun z => p.eval z) ∧
    ∀ z : ℂ, ‖z‖ ≤ R → ‖p.eval z - F z‖ ≤ ε

theorem StripApprox.mono {D D' : ℝ} {F : ℂ → ℂ} (h : StripApprox D F) (hD : D ≤ D') :
    StripApprox D' F := by
  intro R ε hε
  obtain ⟨p, hp, hz, ha⟩ := h R ε hε
  exact ⟨p, hp, fun z hz0 => (hz z hz0).trans hD, ha⟩

theorem StripApprox.of_limit {D : ℝ} {F : ℂ → ℂ} {G : ℕ → ℂ → ℂ}
    (hG : ∀ n, StripApprox D (G n))
    (hlim : ∀ R ε : ℝ, 0 < ε → ∃ n, ∀ z : ℂ, ‖z‖ ≤ R → ‖G n z - F z‖ ≤ ε) :
    StripApprox D F := by
  intro R ε hε
  obtain ⟨n, hn⟩ := hlim R (ε / 2) (by positivity)
  obtain ⟨p, hp, hz, ha⟩ := hG n R (ε / 2) (by positivity)
  refine ⟨p, hp, hz, fun z hzR => ?_⟩
  calc ‖p.eval z - F z‖ = ‖(p.eval z - G n z) + (G n z - F z)‖ := by ring_nf
    _ ≤ ‖p.eval z - G n z‖ + ‖G n z - F z‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (ha z hzR) (hn z hzR)
    _ = ε := by ring

theorem norm_add_I_mul_le (z : ℂ) {l : ℝ} (hl : 0 ≤ l) : ‖z + I * l‖ ≤ ‖z‖ + l := by
  refine (norm_add_le _ _).trans ?_
  simp [abs_of_nonneg hl]

theorem norm_sub_I_mul_le (z : ℂ) {l : ℝ} (hl : 0 ≤ l) : ‖z - I * l‖ ≤ ‖z‖ + l := by
  refine (norm_sub_le _ _).trans ?_
  simp [abs_of_nonneg hl]

theorem StripApprox.shift {D l : ℝ} {F : ℂ → ℂ} (hl : 0 < l) (h : StripApprox D F) :
    StripApprox (max (D - l ^ 2) 0) (shiftAvg l F) := by
  intro R ε hε
  obtain ⟨p, hp, hz, ha⟩ := h (R + l) ε hε
  set q : ℂ[X] := C (1 / 2 : ℂ) * (p.comp (X + C (I * l)) + p.comp (X - C (I * l)))
  have hq : ∀ z, q.eval z = shiftAvg l (fun w => p.eval w) z := by
    intro z; simp [q, eval_comp, shiftAvg]; ring
  have hqf : (fun z => q.eval z) = shiftAvg l (fun w => p.eval w) := funext hq
  refine ⟨q, ?_, ?_, ?_⟩
  · intro z
    rw [hq, hq]
    simp only [shiftAvg, map_div₀, map_add, map_ofNat]
    rw [hp, hp]
    have e1 : starRingEnd ℂ (z + I * l) = starRingEnd ℂ z - I * l := by
      simp [map_add, map_mul, conj_ofReal]; ring
    have e2 : starRingEnd ℂ (z - I * l) = starRingEnd ℂ z + I * l := by
      simp [map_sub, map_mul, conj_ofReal]
    rw [e1, e2]; ring
  · rw [hqf]; exact shiftAvg_poly_strip hp hl hz
  · intro z hzR
    rw [hq]
    have h1 := ha (z + I * l) ((norm_add_I_mul_le z hl.le).trans (by linarith))
    have h2 := ha (z - I * l) ((norm_sub_I_mul_le z hl.le).trans (by linarith))
    simp only [shiftAvg]
    calc ‖(p.eval (z + I * l) + p.eval (z - I * l)) / 2 - (F (z + I * l) + F (z - I * l)) / 2‖
        = ‖(p.eval (z + I * l) - F (z + I * l)) + (p.eval (z - I * l) - F (z - I * l))‖ / 2 := by
          rw [show ∀ a b c d : ℂ, (a + b) / 2 - (c + d) / 2 = ((a - c) + (b - d)) / 2 from
            fun a b c d => by ring, norm_div]
          simp
      _ ≤ (‖p.eval (z + I * l) - F (z + I * l)‖ + ‖p.eval (z - I * l) - F (z - I * l)‖) / 2 := by
          gcongr; exact norm_add_le _ _
      _ ≤ (ε + ε) / 2 := by gcongr
      _ = ε := by ring

theorem max_sub_le (a b : ℝ) (hb : 0 ≤ b) : max (max a 0 - b) 0 ≤ max (a - b) 0 := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h]; exact max_le (by linarith [le_max_right (a - b) 0]) (le_max_right _ _)
  · rw [max_eq_left h]

theorem StripApprox.iterate {D l : ℝ} {F : ℂ → ℂ} (hl : 0 < l) (h : StripApprox D F) :
    ∀ n : ℕ, StripApprox (max (D - n * l ^ 2) 0) ((shiftAvg l)^[n] F) := by
  intro n
  induction n with
  | zero => simpa using h.mono (le_max_left D 0)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine (ih.shift hl).mono ?_
    have := max_sub_le (D - n * l ^ 2) (l ^ 2) (by positivity)
    push_cast
    convert this using 2; ring

theorem StripApprox.differentiable {D : ℝ} {F : ℂ → ℂ} (h : StripApprox D F) :
    Differentiable ℂ F := by
  choose p _ _ hp using fun n : ℕ => h n (1 / ((n : ℝ) + 1)) (by positivity)
  have hT : TendstoLocallyUniformly (fun n z => (p n).eval z) F atTop := by
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε x
    refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
    obtain ⟨N, hN⟩ := exists_nat_gt (max (‖x‖ + 1) (1 / ε))
    filter_upwards [eventually_ge_atTop N] with n hn y hy
    have hn' : max (‖x‖ + 1) (1 / ε) < n := lt_of_lt_of_le hN (by exact_mod_cast hn)
    have hy' : ‖y‖ ≤ n := by
      have : ‖y‖ ≤ ‖x‖ + dist y x := by
        rw [dist_eq_norm]; calc ‖y‖ = ‖x + (y - x)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith [Metric.mem_ball.1 hy, le_max_left (‖x‖ + 1) (1 / ε)]
    rw [dist_eq_norm, norm_sub_rev]
    refine lt_of_le_of_lt (hp n y hy') ?_
    have h1 : 1 / ε < (n : ℝ) + 1 := by linarith [le_max_right (‖x‖ + 1) (1 / ε)]
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at h1
    linarith
  have := (tendstoLocallyUniformlyOn_univ.2 hT).differentiableOn
    (Eventually.of_forall fun n => (p n).differentiable.differentiableOn) isOpen_univ
  exact differentiableOn_univ.1 this

/-- Hurwitz-type closure: a nonzero `StripApprox D` function has all its zeros in the strip. -/
theorem StripApprox.zeros {D : ℝ} {F : ℂ → ℂ} (h : StripApprox D F) (hne : ∃ z, F z ≠ 0) :
    StripZeros D F := by
  intro z0 hz0
  by_contra hlt
  push Not at hlt
  have hF := h.differentiable
  rcases (hF.analyticAt z0).eventually_eq_zero_or_eventually_ne_zero with h0 | hne'
  · obtain ⟨w, hw⟩ := hne
    apply hw
    have := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ => hF.analyticAt z) isPreconnected_univ (mem_univ z0) h0 (mem_univ w)
    simpa using this
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne'
  obtain ⟨ε, hε, hε'⟩ := hne'
  have hstrip : ∀ᶠ z in 𝓝 z0, D < z.im ^ 2 :=
    ((continuous_im.pow 2).tendsto z0).eventually (lt_mem_nhds hlt)
  rw [Metric.eventually_nhds_iff] at hstrip
  obtain ⟨ρ, hρ, hρ'⟩ := hstrip
  set r := min ε ρ / 2 with hr_def
  have hr : 0 < r := by positivity
  have hrε : r < ε := by have := min_le_left ε ρ; linarith
  have hrρ : r < ρ := by have := min_le_right ε ρ; linarith
  have hball : ∀ w, dist w z0 ≤ r → D < w.im ^ 2 := fun w hw => hρ' (by linarith)
  have hsph : ∀ w ∈ Metric.sphere z0 r, F w ≠ 0 := by
    intro w hw
    rw [Metric.mem_sphere] at hw
    refine hε' (by linarith) ?_
    intro hw0; rw [Set.mem_singleton_iff] at hw0; rw [hw0, dist_self] at hw; linarith
  obtain ⟨z1, hz1, hmin⟩ := (isCompact_sphere z0 r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hr.le) hF.continuous.norm.continuousOn
  set m := ‖F z1‖
  have hm : 0 < m := norm_pos_iff.2 (hsph z1 hz1)
  obtain ⟨p, -, hzp, hap⟩ := h (‖z0‖ + r) (m / 3) (by positivity)
  have hnorm : ∀ w, dist w z0 ≤ r → ‖w‖ ≤ ‖z0‖ + r := by
    intro w hw
    rw [dist_eq_norm] at hw
    calc ‖w‖ = ‖z0 + (w - z0)‖ := by ring_nf
      _ ≤ ‖z0‖ + ‖w - z0‖ := norm_add_le _ _
      _ ≤ ‖z0‖ + r := by linarith
  have hpne : ∀ w ∈ Metric.closedBall z0 r, p.eval w ≠ 0 := by
    intro w hw hpw
    have := hzp w hpw
    have := hball w (Metric.mem_closedBall.1 hw)
    linarith
  have hd : DiffContOnCl ℂ (fun w => (p.eval w)⁻¹) (Metric.ball z0 r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z0 hr.ne']
    intro w hw
    exact ((p.differentiable w).inv (hpne w hw)).differentiableWithinAt
  have hC : ∀ w ∈ frontier (Metric.ball z0 r), ‖(p.eval w)⁻¹‖ ≤ (2 * m / 3)⁻¹ := by
    intro w hw
    rw [frontier_ball z0 hr.ne'] at hw
    have hwd : dist w z0 = r := Metric.mem_sphere.1 hw
    have h1 := hap w (hnorm w hwd.le)
    have h2 : m ≤ ‖F w‖ := hmin hw
    have h3 : 2 * m / 3 ≤ ‖p.eval w‖ := by
      have := norm_sub_norm_le (F w) (F w - p.eval w)
      rw [norm_sub_rev] at h1
      simp only [sub_sub_cancel] at this
      linarith
    rw [norm_inv]
    exact inv_anti₀ (by positivity) h3
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd hC
    (subset_closure (Metric.mem_ball_self hr))
  have hp0 : p.eval z0 ≠ 0 := hpne z0 (Metric.mem_closedBall_self hr.le)
  rw [norm_inv, inv_le_inv₀ (norm_pos_iff.2 hp0) (by positivity)] at hmax
  have := hap z0 (by linarith [norm_nonneg z0])
  rw [hz0, sub_zero] at this
  linarith


/-! ## The cosine transform side -/

/-- `∫_0^∞ w(u) cos(z u) du`. -/
def cosT (w : ℝ → ℝ) (z : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), (w u : ℂ) * Complex.cos (z * u)

/-- Rodgers–Tao normalization: `H_t(z) = ∫_0^∞ e^{t u²} Φ(u) cos(z u) du`. -/
def dbnH (Φ : ℝ → ℝ) (t : ℝ) : ℂ → ℂ := cosT (fun u => Real.exp (t * u ^ 2) * Φ u)

/-- Continuous, and `e^{c u} w(u)` integrable on `(0, ∞)` for every real `c`. -/
def Admissible (w : ℝ → ℝ) : Prop :=
  Continuous w ∧ ∀ c : ℝ, IntegrableOn (fun u => Real.exp (c * u) * w u) (Ioi 0)

lemma norm_cos_le (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos, norm_div, Complex.norm_two]
  have h1 : ‖Complex.exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.2; simp [neg_le_abs]
  have h2 : ‖Complex.exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.2; simp [le_abs_self]
  have := norm_add_le (Complex.exp (w * I)) (Complex.exp (-w * I))
  linarith

lemma norm_cos_mul_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.cos (z * u)‖ ≤ Real.exp (‖z‖ * u) := by
  refine (norm_cos_le _).trans (Real.exp_le_exp.2 ?_)
  have : (z * (u : ℂ)).im = z.im * u := by simp
  rw [this, abs_mul, abs_of_nonneg hu]
  exact mul_le_mul_of_nonneg_right (abs_im_le_norm z) hu

lemma continuous_integrand {w : ℝ → ℝ} (hw : Continuous w) (z : ℂ) :
    Continuous (fun u : ℝ => (w u : ℂ) * Complex.cos (z * u)) :=
  (continuous_ofReal.comp hw).mul
    (Complex.continuous_cos.comp (continuous_const.mul continuous_ofReal))

lemma Admissible.integrable_cos {w : ℝ → ℝ} (hw : Admissible w) (z : ℂ) :
    IntegrableOn (fun u : ℝ => (w u : ℂ) * Complex.cos (z * u)) (Ioi 0) := by
  refine Integrable.mono' (hw.2 ‖z‖).norm (continuous_integrand hw.1 z).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_comm (Real.exp _)]
  exact mul_le_mul_of_nonneg_left (norm_cos_mul_le z (le_of_lt hu)) (abs_nonneg _)

lemma Admissible.cosh_mul {w : ℝ → ℝ} (hw : Admissible w) (l : ℝ) :
    Admissible (fun u => Real.cosh (l * u) * w u) := by
  refine ⟨(Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul hw.1, fun c => ?_⟩
  have : (fun u => Real.exp (c * u) * (Real.cosh (l * u) * w u)) =
      fun u => (Real.exp ((c + l) * u) * w u + Real.exp ((c - l) * u) * w u) / 2 := by
    funext u
    rw [Real.cosh_eq, show (c + l) * u = c * u + l * u by ring,
      show (c - l) * u = c * u + -(l * u) by ring, Real.exp_add, Real.exp_add]
    ring
  rw [this]
  exact ((hw.2 (c + l)).add (hw.2 (c - l))).div_const 2

lemma Admissible.cosh_pow_mul {w : ℝ → ℝ} (hw : Admissible w) (l : ℝ) :
    ∀ n : ℕ, Admissible (fun u => Real.cosh (l * u) ^ n * w u) := by
  intro n
  induction n with
  | zero => simpa using hw
  | succ n ih =>
    have := ih.cosh_mul l
    convert this using 2 with u
    ring

lemma admissible_gauss {Φ : ℝ → ℝ} (hΦc : Continuous Φ)
    (hΦ : ∀ a : ℝ, IntegrableOn (fun u => Real.exp (a * u ^ 2) * Φ u) (Ioi 0)) (t : ℝ) :
    Admissible (fun u => Real.exp (t * u ^ 2) * Φ u) := by
  refine ⟨(Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))).mul hΦc,
    fun c => ?_⟩
  refine Integrable.mono' (((hΦ (t + 1)).norm).const_mul (Real.exp (c ^ 2 / 4)))
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))).mul
        hΦc)).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (abs_nonneg _)
  nlinarith [sq_nonneg (u - c / 2)]

/-- The shift average on the `z` side is the `cosh` multiplier on the `u` side. -/
theorem shiftAvg_cosT {w : ℝ → ℝ} (hw : Admissible w) (l : ℝ) :
    shiftAvg l (cosT w) = cosT (fun u => Real.cosh (l * u) * w u) := by
  funext z
  simp only [shiftAvg, cosT]
  rw [← integral_add (hw.integrable_cos _) (hw.integrable_cos _), ← integral_div]
  congr 1
  funext u
  have e1 : (z + I * l) * u = z * u + ((l * u : ℝ) : ℂ) * I := by push_cast; ring
  have e2 : (z - I * l) * u = z * u - ((l * u : ℝ) : ℂ) * I := by push_cast; ring
  rw [e1, e2, Complex.cos_add, Complex.cos_sub, Complex.cos_mul_I]
  push_cast
  ring

theorem iterate_shiftAvg_cosT {w : ℝ → ℝ} (hw : Admissible w) (l : ℝ) :
    ∀ n : ℕ, (shiftAvg l)^[n] (cosT w) = cosT (fun u => Real.cosh (l * u) ^ n * w u) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, shiftAvg_cosT (hw.cosh_pow_mul l n)]
    congr 1
    funext u
    ring

lemma one_add_sq_div_two_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h2 : Real.cosh x = 1 + 2 * Real.sinh (x / 2) ^ 2 := by
    have := Real.cosh_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at this
    rw [this, Real.cosh_sq]; ring
  have h3 : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := by
    rw [← sq_abs (x / 2), ← sq_abs (Real.sinh (x / 2)), Real.abs_sinh]
    exact pow_le_pow_left₀ (abs_nonneg _) (Real.self_le_sinh_iff.2 (abs_nonneg _)) 2
  rw [h2]; nlinarith

lemma cosh_pow_le {t : ℝ} (ht : 0 ≤ t) (u : ℝ) (n : ℕ) :
    Real.cosh (Real.sqrt (2 * t / n) * u) ^ n ≤ Real.exp (t * u ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using Real.one_le_exp (by positivity : 0 ≤ t * u ^ 2)
  · calc Real.cosh (Real.sqrt (2 * t / n) * u) ^ n
        ≤ Real.exp ((Real.sqrt (2 * t / n) * u) ^ 2 / 2) ^ n :=
          pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) n
      _ = Real.exp (t * u ^ 2) := by
          rw [← Real.exp_nat_mul, mul_pow, Real.sq_sqrt (by positivity)]
          congr 1
          field_simp

lemma cosh_pow_tendsto {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    Tendsto (fun n : ℕ => Real.cosh (Real.sqrt (2 * t / n) * u) ^ n) atTop
      (𝓝 (Real.exp (t * u ^ 2))) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (Real.tendsto_one_add_div_pow_exp (t * u ^ 2))
    tendsto_const_nhds ?_ (Eventually.of_forall (cosh_pow_le ht u))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine pow_le_pow_left₀ (by positivity) ?_ n
  have := one_add_sq_div_two_le_cosh (Real.sqrt (2 * t / n) * u)
  rw [mul_pow, Real.sq_sqrt (by positivity)] at this
  convert this using 1
  field_simp

lemma cosT_sub_norm_le {w₁ w₂ : ℝ → ℝ} (h₁ : Admissible w₁) (h₂ : Admissible w₂) {z : ℂ}
    {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖cosT w₁ z - cosT w₂ z‖ ≤ ∫ u in Ioi (0 : ℝ), |w₁ u - w₂ u| * Real.exp (R * u) := by
  unfold cosT
  rw [← integral_sub (h₁.integrable_cos z) (h₂.integrable_cos z)]
  have hg : IntegrableOn (fun u => |w₁ u - w₂ u| * Real.exp (R * u)) (Ioi 0) := by
    have := ((h₁.2 R).sub (h₂.2 R)).abs
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [Pi.sub_apply]
    rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  refine norm_integral_le_of_norm_le hg (ae_restrict_of_forall_mem measurableSet_Ioi ?_)
  intro u hu
  rw [← sub_mul, norm_mul, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ((norm_cos_mul_le z (le_of_lt hu)).trans ?_) (abs_nonneg _)
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hz (le_of_lt hu))

lemma tendsto_weight_error {Φ : ℝ → ℝ} (hΦc : Continuous Φ)
    (hΦ : ∀ a : ℝ, IntegrableOn (fun u => Real.exp (a * u ^ 2) * Φ u) (Ioi 0)) {t : ℝ}
    (ht : 0 ≤ t) (R : ℝ) :
    Tendsto (fun n : ℕ => ∫ u in Ioi (0 : ℝ),
      |Real.cosh (Real.sqrt (2 * t / n) * u) ^ n * Φ u - Real.exp (t * u ^ 2) * Φ u| *
        Real.exp (R * u)) atTop (𝓝 0) := by
  have hb := ((admissible_gauss hΦc hΦ t).2 R).abs.const_mul 2
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (n : ℕ) u => |Real.cosh (Real.sqrt (2 * t / n) * u) ^ n * Φ u -
      Real.exp (t * u ^ 2) * Φ u| * Real.exp (R * u))
    (f := fun _ => 0) _ (fun n => ?_) hb (fun n => ?_) ?_
  · simpa using hlim
  · exact (((((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).pow n).mul hΦc).sub
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))).mul hΦc)).abs.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    have h1 := cosh_pow_le ht u n
    have h0 : 0 ≤ Real.cosh (Real.sqrt (2 * t / n) * u) ^ n :=
      pow_nonneg (Real.cosh_pos _).le n
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
    have : |Real.cosh (Real.sqrt (2 * t / n) * u) ^ n - Real.exp (t * u ^ 2)| ≤
        2 * Real.exp (t * u ^ 2) := by
      rw [abs_le]; constructor <;> nlinarith [Real.exp_pos (t * u ^ 2)]
    have hR := Real.exp_pos (R * u)
    have hΦa := abs_nonneg (Φ u)
    rw [← sub_mul, abs_mul]
    calc |Real.cosh (Real.sqrt (2 * t / n) * u) ^ n - Real.exp (t * u ^ 2)| * |Φ u| *
          Real.exp (R * u) ≤ 2 * Real.exp (t * u ^ 2) * |Φ u| * Real.exp (R * u) := by gcongr
      _ = 2 * (Real.exp (R * u) * (Real.exp (t * u ^ 2) * |Φ u|)) := by ring
  · refine Eventually.of_forall fun u => ?_
    have := (((cosh_pow_tendsto ht u).mul_const (Φ u)).sub_const
      (Real.exp (t * u ^ 2) * Φ u)).abs.mul_const (Real.exp (R * u))
    simpa using this

lemma admissible_of_gauss {Φ : ℝ → ℝ} (hΦc : Continuous Φ)
    (hΦ : ∀ a : ℝ, IntegrableOn (fun u => Real.exp (a * u ^ 2) * Φ u) (Ioi 0)) :
    Admissible Φ := by
  simpa using admissible_gauss hΦc hΦ 0

lemma dbnH_zero_eq (Φ : ℝ → ℝ) : dbnH Φ 0 = cosT Φ := by
  simp [dbnH]

/-- **Strip approximability flows forward under the heat flow.** -/
theorem stripApprox_dbnH {Φ : ℝ → ℝ} (hΦc : Continuous Φ)
    (hΦ : ∀ a : ℝ, IntegrableOn (fun u => Real.exp (a * u ^ 2) * Φ u) (Ioi 0)) {D t : ℝ}
    (ht : 0 < t) (h0 : StripApprox D (dbnH Φ 0)) :
    StripApprox (max (D - 2 * t) 0) (dbnH Φ t) := by
  have hA := admissible_of_gauss hΦc hΦ
  rw [dbnH_zero_eq] at h0
  set l : ℕ → ℝ := fun n => Real.sqrt (2 * t / n)
  refine StripApprox.of_limit (G := fun n => (shiftAvg (l (n + 1)))^[n + 1] (cosT Φ))
    (fun n => ?_) (fun R ε hε => ?_)
  · have hl : 0 < l (n + 1) := Real.sqrt_pos.2 (by positivity)
    have := h0.iterate hl (n + 1)
    convert this using 2
    simp only [l]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  · have hT := (tendsto_weight_error hΦc hΦ ht.le R).comp (tendsto_add_atTop_nat 1)
    obtain ⟨n, hn⟩ := (hT.eventually (gt_mem_nhds hε)).exists
    refine ⟨n, fun z hz => ?_⟩
    simp only [iterate_shiftAvg_cosT hA]
    refine (cosT_sub_norm_le (hA.cosh_pow_mul _ _) (admissible_gauss hΦc hΦ t) hz).trans ?_
    simp only [Function.comp_apply] at hn
    push_cast at hn
    simp only [l]
    push_cast
    exact hn.le


/-! ## de Bruijn's strip contraction and the bound on `Λ` -/

lemma dbnH_at_zero_ne {Φ : ℝ → ℝ}
    (hΦ : ∀ a : ℝ, IntegrableOn (fun u => Real.exp (a * u ^ 2) * Φ u) (Ioi 0))
    (hpos : ∀ u, 0 < u → 0 ≤ Φ u) (hint : 0 < ∫ u in Ioi (0 : ℝ), Φ u) {t : ℝ} (ht : 0 ≤ t) :
    dbnH Φ t 0 ≠ 0 := by
  simp only [dbnH, cosT, zero_mul, Complex.cos_zero, mul_one]
  rw [integral_complex_ofReal, ofReal_ne_zero]
  refine (lt_of_lt_of_le hint ?_).ne'
  refine setIntegral_mono_on (by simpa using hΦ 0) (hΦ t) measurableSet_Ioi (fun u hu => ?_)
  exact le_mul_of_one_le_left (hpos u hu) (Real.one_le_exp (by positivity))

/-- **de Bruijn's strip contraction** (1950, for this class): if `H_0` is a locally uniform limit
of real polynomials with all zeros in `(Im z)² ≤ D`, then for `t > 0` every zero of `H_t`
satisfies `(Im z)² ≤ max (D − 2t) 0`. -/
theorem deBruijn_strip {Φ : ℝ → ℝ} (hΦc : Continuous Φ)
    (hΦ : ∀ a : ℝ, IntegrableOn (fun u => Real.exp (a * u ^ 2) * Φ u) (Ioi 0))
    (hpos : ∀ u, 0 < u → 0 ≤ Φ u) (hint : 0 < ∫ u in Ioi (0 : ℝ), Φ u) {D t : ℝ} (ht : 0 < t)
    (h0 : StripApprox D (dbnH Φ 0)) :
    StripZeros (max (D - 2 * t) 0) (dbnH Φ t) :=
  (stripApprox_dbnH hΦc hΦ ht h0).zeros ⟨0, dbnH_at_zero_ne hΦ hpos hint ht.le⟩

/-- The times `t` at which `H_t` has only real zeros. -/
def dbnRealZeroTimes (Φ : ℝ → ℝ) : Set ℝ := {t | ∀ z, dbnH Φ t z = 0 → z.im = 0}

/-- `Λ = inf {t : H_t has only real zeros}` (in `EReal`, so no boundedness side condition). -/
def dbnLambda (Φ : ℝ → ℝ) : EReal := sInf ((fun t : ℝ => (t : EReal)) '' dbnRealZeroTimes Φ)

theorem real_zeros_of_strip {Φ : ℝ → ℝ} (hΦc : Continuous Φ)
    (hΦ : ∀ a : ℝ, IntegrableOn (fun u => Real.exp (a * u ^ 2) * Φ u) (Ioi 0))
    (hpos : ∀ u, 0 < u → 0 ≤ Φ u) (hint : 0 < ∫ u in Ioi (0 : ℝ), Φ u) {D : ℝ} (hD : 0 ≤ D)
    (h0 : StripApprox D (dbnH Φ 0)) {t : ℝ} (ht : D / 2 ≤ t) : t ∈ dbnRealZeroTimes Φ := by
  intro z hz
  have hsq : z.im ^ 2 ≤ 0 := by
    rcases lt_or_eq_of_le (le_trans (by linarith : (0 : ℝ) ≤ D / 2) ht) with htp | ht0
    · have := deBruijn_strip hΦc hΦ hpos hint htp h0 z hz
      rwa [max_eq_right (by linarith)] at this
    · subst ht0
      have := h0.zeros ⟨0, dbnH_at_zero_ne hΦ hpos hint le_rfl⟩ z hz
      linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hsq (sq_nonneg _))

/-- **`Λ_le_of_strip`**: strip half-width `Δ` (`D = Δ²`) for `H_0` gives `Λ ≤ Δ²/2`. -/
theorem Λ_le_of_strip {Φ : ℝ → ℝ} (hΦc : Continuous Φ)
    (hΦ : ∀ a : ℝ, IntegrableOn (fun u => Real.exp (a * u ^ 2) * Φ u) (Ioi 0))
    (hpos : ∀ u, 0 < u → 0 ≤ Φ u) (hint : 0 < ∫ u in Ioi (0 : ℝ), Φ u) {D : ℝ} (hD : 0 ≤ D)
    (h0 : StripApprox D (dbnH Φ 0)) : dbnLambda Φ ≤ ((D / 2 : ℝ) : EReal) :=
  sInf_le ⟨D / 2, real_zeros_of_strip hΦc hΦ hpos hint hD h0 le_rfl, rfl⟩

/-! ## The quasi-RH constant

With `H_0(z) = (1/8) ξ(1/2 + i z/2)` (Rodgers–Tao normalization), a zero `z` of `H_0`
corresponds to the nontrivial zero `ρ = 1/2 + i z/2`, and `Im z = −2 (Re ρ − 1/2)`. -/

theorem im_of_xi_param (z : ℂ) : z.im = -2 * ((1 / 2 + I * z / 2 : ℂ).re - 1 / 2) := by
  simp; ring

/-- `QuasiRH` (no zeros with `Re s > 7/8`) puts every zero of `ξ(1/2 + i z/2)` in
`(Im z)² ≤ (3/4)²`. -/
theorem quasiRH_xi_strip (h : QuasiRHWiring.QuasiRH) {z : ℂ}
    (hz : Reduction.IsNontrivialZero (1 / 2 + I * z / 2)) : z.im ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by
  have h1 := QuasiRHWiring.abs_half_sub_re_le h hz
  have h2 : |z.im| ≤ 3 / 4 := by
    rw [im_of_xi_param z, abs_mul, abs_neg, abs_two, abs_sub_comm]
    linarith
  calc z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
    _ ≤ (3 / 4) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2

/-- The quasi-RH instance: strip `(Im z)² ≤ (3/4)²` for `H_0` gives `Λ ≤ 9/32`. -/
theorem Λ_le_nine_thirtyseconds {Φ : ℝ → ℝ} (hΦc : Continuous Φ)
    (hΦ : ∀ a : ℝ, IntegrableOn (fun u => Real.exp (a * u ^ 2) * Φ u) (Ioi 0))
    (hpos : ∀ u, 0 < u → 0 ≤ Φ u) (hint : 0 < ∫ u in Ioi (0 : ℝ), Φ u)
    (h0 : StripApprox ((3 / 4 : ℝ) ^ 2) (dbnH Φ 0)) : dbnLambda Φ ≤ ((9 / 32 : ℝ) : EReal) := by
  have := Λ_le_of_strip hΦc hΦ hpos hint (by norm_num) h0
  norm_num at this ⊢
  exact this

/-- `9/32` exceeds the Platt–Trudgian record `0.2`. -/
theorem nine_thirtyseconds_gt_record : (1 / 5 : ℝ) < 9 / 32 := by norm_num

end FleetDeBruijnNewman
