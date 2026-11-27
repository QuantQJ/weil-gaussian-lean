import FleetHeadContourStrip
import FleetHeatPositivityRH
import ZetaStrip

/-!
# Sra's smoothed heat sums and hp-proof's Gaussian windows

Source: S. Sra, *Some positivity properties of Riemann Ξ under smoothing*, TU Munich, v1, 11 Nov 2026
(github.com/suvrit/preprints, `riem-xi-smoothing`). Also: S. Sra, *On some positivity properties of the
Riemann Ξ function*, arXiv:2611.02944 (2 Nov 2026); P. Freitas, *A Li-type criterion for zero-free half-planes
of Riemann's zeta function*, arXiv:math/0507368 (J. London Math. Soc.).

## Dictionary
Sra smooths each zero `z_ρ = γ − i(β − ½)` (= hp-proof's `ordinate ρ`) by a density `K` and studies
`p_K(x) = ½ Σ_{γ>0} (K(x − z_ρ) + K(x + z_ρ))`, `P_K(x) = 2∫₀ˣ p_K`. For the Gaussian `G_σ` (half-variance
`σ`), `gaussHat b α z = 2π G_b(α − z)` (`gaussHat_eq_sraGauss`), so hp-proof's zero trace
`R_b(α) = Σ_ρ ĝ_{b,α}(z_ρ)` is `4π p_b(α)` in Sra's notation (real part, zeros paired by conjugation), with
hp-proof's `b` = Sra's Gaussian half-variance `σ`. `RH_iff_heat_positivity` is the hp-proof form of Sra's Proposition 3.2
(`σ_H = 0 ⟺ RH`). At `α = 0`, `R_b(0) = √(π/b) Σ_ρ e^{−t z_ρ²}`, `t = 1/(4b)` (`zeroTrace_zero_eq_heat`): the
heat sum of arXiv:2611.02944, Theorem 1.1.

## The two 1/8's
hp-proof: a window rate `c` gives the strip `|β − ½| ≤ √(2c)` (`zeros_in_strip_of_window_rate`), so `c = h²/2`
for half-width `h`. The `h²` comes from the Gaussian's edge growth `|G_b(x + iy)| = G_b(x) e^{y²/(4b)}`
(`norm_sraGauss_shift`, `norm_sraGauss_edge`): head exponent `h²/4` (`= 1/16` at `h = ½`), doubled by
Cauchy–Schwarz for the squared window. Sra: the least half-variance of a kernel positive on every horizontal line
of the strip `|Im| < h` is `Var(K_h)/2 = h²/2` (his Theorem 2.3(ii); `K_h` the strip Poisson kernel). Both are
`h ↦ h²/2` (`sqrt_two_mul_half_sq`), and both give `1/8` at `h = ½` (`sqrt_two_mul_one_eighth`), but they are
different quantities: `c` is a growth exponent of one fixed kernel (the Gaussian) as `b → 0`, Sra's `1/8` is a
minimal width over all strip-holomorphic kernels. For the Gaussian itself Sra's termwise threshold does not exist
(`exists_re_sraGauss_neg`). The quantity the two papers share exactly is the edge exponent `1/16`: hp-proof's
trivial head rate (`FleetExponentLadder`) and Sra's Gaussian scale `σ_T = 1/(16 log T)`.

## Why Sra's π²/288 is an averaged statement
Sra's Theorem 2.5 takes the band-limited `κ₆` (Fourier support `[−12, 12]`, half-variance `π²/288`) and applies the
Guinand–Weil explicit formula: `πP_{κ₆}(x)` = a finite signed sum over prime powers `n < e¹²` + gamma-factor
(Riemann–Siegel θ) term + pole term (his (B.1)). Interval arithmetic certifies `P_{κ₆}(x) ≥ 10⁻⁸ min(x,1)` on
`(0, 60]`; a θ-bound gives `P > 3/4` for `x ≥ 60`. The conclusion is the sign of `P_{κ₆}`, the cumulative profile
summed over all zeros at once; it is not a sign for each zero's term. A termwise version at half-variance `w`
would force `|β − ½| ≤ √(2w)` for every zero (Theorem 2.3(ii)), i.e. `π/12` at `w = π²/288`
(`sqrt_two_mul_pi_sq_div_288`); the same strip is what a window rate `π²/288` would give
(`zeros_in_strip_of_window_rate_pi_sq_div_288`). That strip is not known.

## What is proved here (unconditional)
* Sra's Lemma 2.4 for the strip Poisson kernel (`re_sechKernel_shift`, `re_sechKernel_shift_pos`) and termwise
  positivity at every nontrivial zero (`sechKernel_zero_term_pos`).
* Second smoothing: `K_{1/2} ∗ G_b` (half-variance `1/8 + b`) is positive at every `u − z_ρ`
  (`sechGauss_zero_term_pos`).
* The α-average of hp-proof's zero-trace term against `K_{1/2}` equals `2π (K_{1/2} ∗ G_b)(α − z)`
  (`integral_sech_gaussHat`, a horizontal contour shift `integral_line_shift`), and the full averaged trace
  `∫ K_{1/2}(α − α') R_b(α') dα'` is the absolutely convergent sum of these terms (`hasSum_sech_zeroTrace`).
  Hence `Re ∫ K_{1/2}(α − α') R_b(α') dα' ≥ 0` for every `b > 0`, `α`, with `> 0` once a zero is given
  (`re_sech_zeroTrace_nonneg`, `re_sech_zeroTrace_pos`). This is Sra's strip-only level (`1/8`) carried by
  hp-proof's window centres.
* Freitas: `‖ρ/(ρ − τ)‖ ≤ 1 ⟺ Re ρ ≤ τ/2` (`norm_div_sub_le_one_iff`); a window rate `c` puts every term
  `(ρ/(ρ − τ))ⁿ` of his `α_n(τ)`, `τ = 1 + 2√(2c)`, in the closed unit disk (`freitas_terms_le_one_of_window_rate`).

## Not proved here
Sra's `π²/288` certificate (computer-assisted interval arithmetic over prime powers below `e¹²` plus Stirling
bounds for θ) and his verified-height results (Platt–Trudgian to `3·10¹²`) are not formalized. The positivity of
Freitas's `α_n(τ)` and the PF-order results of arXiv:2611.02944 are not formalized.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real Interval
open OffLineDetection Reduction ZeroSumLimit GaussianTest

namespace FleetSraSmoothing

/-! ## Part 1. The Gaussian dictionary -/

/-- Sra's normalized Gaussian `G_σ(w) = (4πσ)^{-1/2} exp(−w²/(4σ))` (variance `2σ`, half-variance `σ`). -/
def sraGauss (σ : ℝ) (w : ℂ) : ℂ :=
  ((1 / Real.sqrt (4 * π * σ) : ℝ) : ℂ) * Complex.exp (-w ^ 2 / (4 * σ))

/-- **Dictionary.** hp-proof's Gaussian zero-trace term is `2π` times Sra's Gaussian of half-variance `b`:
`gaussHat b α z = 2π · G_b(α − z)`. -/
theorem gaussHat_eq_sraGauss {b : ℝ} (hb : 0 < b) (α : ℝ) (z : ℂ) :
    gaussHat b α z = 2 * π * sraGauss b ((α : ℂ) - z) := by
  rw [gaussHat_eq hb, sraGauss]
  have hs : Real.sqrt (π / b) = 2 * π * (1 / Real.sqrt (4 * π * b)) := by
    have h4 : Real.sqrt (4 * π * b) = 2 * Real.sqrt (π * b) := by
      rw [show 4 * π * b = 2 ^ 2 * (π * b) by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    have hpb : 0 < Real.sqrt (π * b) := Real.sqrt_pos.2 (by positivity)
    rw [h4, Real.sqrt_div' _ hb.le]
    have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
    have hspb : Real.sqrt (π * b) = Real.sqrt π * Real.sqrt b := Real.sqrt_mul Real.pi_pos.le b
    have hspi : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
    rw [hspb]; field_simp; nlinarith [hspi]
  rw [hs]; push_cast
  rw [show ((α : ℂ) - z) ^ 2 = (z - α) ^ 2 by ring]
  ring

/-- `‖G_σ(x + i y)‖ = G_σ(x) · e^{y²/(4σ)}`: the growth of the Gaussian inside the strip. -/
theorem norm_sraGauss_shift {σ : ℝ} (hσ : 0 < σ) (x y : ℝ) :
    ‖sraGauss σ ((x : ℂ) + y * I)‖ = ‖sraGauss σ x‖ * Real.exp (y ^ 2 / (4 * σ)) := by
  unfold sraGauss
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, mul_assoc (‖_‖), ← Real.exp_add]
  congr 2
  rw [show (4 * (σ : ℂ)) = ((4 * σ : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re,
    Complex.div_ofReal_re]
  simp only [neg_re, sq, mul_re, add_re, ofReal_re, mul_im, ofReal_im, I_re, I_im, add_im]
  field_simp
  ring

/-- At the edge of the critical strip (`y = ½`) the Gaussian of half-variance `σ` is amplified by
`e^{1/(16σ)}`. This `1/16` is hp-proof's trivial head exponent (`FleetExponentLadder`) and Sra's constant in
`σ_T = 1/(16 log T)`. -/
theorem norm_sraGauss_edge {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    ‖sraGauss σ ((x : ℂ) + ((1 / 2 : ℝ) : ℂ) * I)‖ = ‖sraGauss σ x‖ * Real.exp (1 / (16 * σ)) := by
  rw [norm_sraGauss_shift hσ]
  congr 2
  field_simp
  ring

/-- Sra's real-part formula: `Re G_σ(u + i d) = |G_σ(u)| e^{d²/(4σ)} cos(u d/(2σ))`. -/
theorem re_sraGauss_shift {σ : ℝ} (hσ : 0 < σ) (u d : ℝ) :
    (sraGauss σ ((u : ℂ) + d * I)).re
      = ‖sraGauss σ u‖ * Real.exp (d ^ 2 / (4 * σ)) * Real.cos (u * d / (2 * σ)) := by
  have hpol : sraGauss σ ((u : ℂ) + d * I)
      = (((1 / Real.sqrt (4 * π * σ)) * Real.exp ((d ^ 2 - u ^ 2) / (4 * σ)) : ℝ) : ℂ)
        * Complex.exp (((-(u * d / (2 * σ))) : ℝ) * I) := by
    unfold sraGauss
    push_cast
    simp only [mul_assoc, ← Complex.exp_add]
    congr 2
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [hpol, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have hn : ‖sraGauss σ u‖ = (1 / Real.sqrt (4 * π * σ)) * Real.exp (-u ^ 2 / (4 * σ)) := by
    unfold sraGauss
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.norm_exp]
    congr 2
    rw [show (4 * (σ : ℂ)) = ((4 * σ : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
    simp [sq]
  rw [hn, show (d ^ 2 - u ^ 2) / (4 * σ) = -u ^ 2 / (4 * σ) + d ^ 2 / (4 * σ) by ring, Real.exp_add]
  ring

/-- **The Gaussian is never termwise positive off the line.** For every displacement `d ≠ 0` the real part
of `G_σ(· + i d)` takes a negative value. So a positive statement about Gaussian-smoothed zero sums that allows
off-line zeros cannot hold zero by zero: it is a statement about the whole sum. -/
theorem exists_re_sraGauss_neg {σ : ℝ} (hσ : 0 < σ) {d : ℝ} (hd : d ≠ 0) :
    ∃ u : ℝ, (sraGauss σ ((u : ℂ) + d * I)).re < 0 := by
  refine ⟨2 * π * σ / d, ?_⟩
  rw [re_sraGauss_shift hσ]
  have hc : Real.cos (2 * π * σ / d * d / (2 * σ)) = -1 := by
    rw [show 2 * π * σ / d * d / (2 * σ) = π by field_simp]
    exact Real.cos_pi
  rw [hc]
  have hn : 0 < ‖sraGauss σ ((2 * π * σ / d : ℝ) : ℂ)‖ := by
    unfold sraGauss
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_pos (abs_pos.2 (ne_of_gt (by positivity))) (norm_pos_iff.2 (Complex.exp_ne_zero _))
  have := Real.exp_pos (d ^ 2 / (4 * σ))
  nlinarith [mul_pos hn this]

/-! ## Part 2. The strip Poisson kernel (Sra, Lemma 2.4 and Theorem 2.3(i)) -/

/-- The hyperbolic-secant density `K_a(z) = (1/(2a)) sech(π z/(2a))` (variance `a²`), the Poisson kernel of the
strip `|Im z| < a`. -/
def sechKernel (a : ℝ) (z : ℂ) : ℂ := ((1 / (2 * a) : ℝ) : ℂ) / Complex.cosh (π * z / (2 * a))

lemma cosh_add_mul_I (U V : ℝ) :
    Complex.cosh ((U : ℂ) + V * I)
      = ((Real.cosh U * Real.cos V : ℝ) : ℂ) + ((Real.sinh U * Real.sin V : ℝ) : ℂ) * I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  push_cast
  ring

lemma normSq_cosh_add_mul_I (U V : ℝ) :
    Complex.normSq (Complex.cosh ((U : ℂ) + V * I)) = Real.sinh U ^ 2 + Real.cos V ^ 2 := by
  rw [cosh_add_mul_I, Complex.normSq_add_mul_I]
  have h1 := Real.cosh_sq U
  have h2 := Real.sin_sq_add_cos_sq V
  nlinarith [h1, h2]

lemma sechKernel_arg (a : ℝ) (ha : 0 < a) (x d : ℝ) :
    (π : ℂ) * ((x : ℂ) + d * I) / (2 * a) = ((π * x / (2 * a) : ℝ) : ℂ) + ((π * d / (2 * a) : ℝ) : ℂ) * I := by
  have : (2 * (a : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * a) ≠ 0)
  push_cast
  field_simp

/-- **Sra, Lemma 2.4.** With `U = πx/(2a)`, `V = πd/(2a)`:
`Re K_a(x + i d) = cosh U cos V / (2a (sinh² U + cos² V))`. -/
theorem re_sechKernel_shift {a : ℝ} (ha : 0 < a) (x d : ℝ) :
    (sechKernel a ((x : ℂ) + d * I)).re
      = Real.cosh (π * x / (2 * a)) * Real.cos (π * d / (2 * a))
        / (2 * a * (Real.sinh (π * x / (2 * a)) ^ 2 + Real.cos (π * d / (2 * a)) ^ 2)) := by
  unfold sechKernel
  rw [sechKernel_arg a ha, Complex.div_re, normSq_cosh_add_mul_I, cosh_add_mul_I]
  simp only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im]
  field_simp
  ring

/-- **Sra, Lemma 2.4 (positivity).** For `|d| < a`, `Re K_a(x + i d) > 0` for every real `x`. -/
theorem re_sechKernel_shift_pos {a : ℝ} (ha : 0 < a) (x : ℝ) {d : ℝ} (hd : |d| < a) :
    0 < (sechKernel a ((x : ℂ) + d * I)).re := by
  rw [re_sechKernel_shift ha]
  have hV : |π * d / (2 * a)| < π / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0:ℝ) < 2 * a),
      div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hc : 0 < Real.cos (π * d / (2 * a)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [abs_lt.1 hV]
  have hch := Real.cosh_pos (π * x / (2 * a))
  positivity

/-- `‖K_a(x + i d)‖ ≤ 1/(2a cos V)`: the kernel is bounded on every interior horizontal line. -/
theorem norm_sechKernel_shift_le {a : ℝ} (ha : 0 < a) (x : ℝ) {d : ℝ} (hd : |d| < a) :
    ‖sechKernel a ((x : ℂ) + d * I)‖ ≤ 1 / (2 * a) / Real.cos (π * d / (2 * a)) := by
  have hV : |π * d / (2 * a)| < π / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0:ℝ) < 2 * a),
      div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hc : 0 < Real.cos (π * d / (2 * a)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [abs_lt.1 hV]
  unfold sechKernel
  rw [sechKernel_arg a ha, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * a))]
  apply div_le_div_of_nonneg_left (by positivity) hc
  have hn : Real.cos (π * d / (2 * a)) ^ 2 ≤ ‖Complex.cosh (((π * x / (2 * a) : ℝ) : ℂ)
      + ((π * d / (2 * a) : ℝ) : ℂ) * I)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, normSq_cosh_add_mul_I]
    nlinarith [sq_nonneg (Real.sinh (π * x / (2 * a)))]
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg (Complex.cosh (((π * x / (2 * a) : ℝ) : ℂ) + ((π * d / (2 * a) : ℝ) : ℂ) * I))]

/-- `u − z_ρ = (u − γ) + i (β − ½)` for `z_ρ = ordinate ρ = γ − i(β − ½)`. -/
lemma sub_ordinate_eq (u : ℝ) (ρ : ℂ) :
    (u : ℂ) - ordinate ρ = ((u - ρ.im : ℝ) : ℂ) + ((ρ.re - 1 / 2 : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [ordinate, sub_eq_add_neg]

/-- Every nontrivial zero has displacement `|β − ½| < ½` (the open critical strip). -/
lemma abs_displacement_lt (x : Index) : |(canonical x).re - 1 / 2| < 1 / 2 := by
  have h := x.1.2
  have h0 := ZetaStrip.re_pos_of_isNontrivialZero h
  have h1 := ZetaStrip.re_lt_one_of_isNontrivialZero h
  rw [abs_lt]; constructor <;> simp only [canonical] <;> linarith

/-- **Strip-only termwise positivity (Sra, Theorem 2.3(i), zero by zero).** For every nontrivial zero `ρ`
(counted in hp-proof's `Index`) and every real `u`, the strip Poisson kernel `K_{1/2}` centred at the complex
point `z_ρ` has positive real part at `u`. Half-variance of `K_{1/2}`: `1/8`. -/
theorem sechKernel_zero_term_pos (x : Index) (u : ℝ) :
    0 < (sechKernel (1 / 2) ((u : ℂ) - ordinate (canonical x))).re := by
  rw [sub_ordinate_eq]
  exact re_sechKernel_shift_pos (by norm_num) _ (abs_displacement_lt x)

/-! ## Part 3. Second smoothing: the sech-averaged Gaussian -/

/-- `G_σ` is real and positive on the real line. -/
lemma sraGauss_ofReal {σ : ℝ} (s : ℝ) :
    sraGauss σ (s : ℂ) = (((1 / Real.sqrt (4 * π * σ)) * Real.exp (-s ^ 2 / (4 * σ)) : ℝ) : ℂ) := by
  unfold sraGauss
  push_cast
  ring_nf

/-- The composite kernel `(K_{1/2} ∗ G_b)(w) = ∫ K_{1/2}(w − s) G_b(s) ds`, evaluated at a complex point `w`.
It is the Gaussian of half-variance `b` smoothed a second time by the strip Poisson kernel; its half-variance is
`1/8 + b`. -/
def sechGauss (b : ℝ) (w : ℂ) : ℂ := ∫ s : ℝ, sechKernel (1 / 2) (w - s) * sraGauss b s

lemma sechKernel_shift_sub (u d s : ℝ) :
    ((u : ℂ) + d * I) - (s : ℂ) = (((u - s : ℝ)) : ℂ) + d * I := by push_cast; ring

lemma continuous_sechKernel_line {a : ℝ} (ha : 0 < a) {d : ℝ} (hd : |d| < a) (u : ℝ) :
    Continuous (fun s : ℝ => sechKernel a (((u : ℂ) + d * I) - (s : ℂ))) := by
  have hne : ∀ s : ℝ, Complex.cosh (π * ((((u : ℂ) + d * I) - (s : ℂ))) / (2 * a)) ≠ 0 := by
    intro s h
    have hp := re_sechKernel_shift_pos ha (u - s) hd
    rw [← sechKernel_shift_sub u d s] at hp
    unfold sechKernel at hp
    rw [h, div_zero, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  unfold sechKernel
  apply Continuous.div continuous_const _ hne
  fun_prop

lemma integrable_sechGauss_integrand {b : ℝ} (hb : 0 < b) (u : ℝ) {d : ℝ} (hd : |d| < 1 / 2) :
    Integrable (fun s : ℝ => sechKernel (1 / 2) (((u : ℂ) + d * I) - s) * sraGauss b s) := by
  have hg : Integrable (fun s : ℝ => sraGauss b (s : ℂ)) := by
    simp_rw [sraGauss_ofReal]
    apply Integrable.ofReal
    apply Integrable.const_mul
    have h := integrable_exp_neg_mul_sq (b := 1 / (4 * b)) (by positivity)
    refine h.congr (Eventually.of_forall fun s => ?_)
    simp only
    congr 1
    ring
  refine hg.bdd_mul (c := 1 / (2 * (1 / 2)) / Real.cos (π * d / (2 * (1 / 2))))
    (continuous_sechKernel_line (by norm_num) hd u).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [sechKernel_shift_sub]
  exact norm_sechKernel_shift_le (by norm_num) _ hd

/-- **Termwise positivity after a second smoothing.** For `b > 0` and `|d| < ½`,
`Re (K_{1/2} ∗ G_b)(u + i d) > 0` for every real `u`. -/
theorem re_sechGauss_pos {b : ℝ} (hb : 0 < b) (u : ℝ) {d : ℝ} (hd : |d| < 1 / 2) :
    0 < (sechGauss b ((u : ℂ) + d * I)).re := by
  unfold sechGauss
  have hint := integrable_sechGauss_integrand hb u hd
  have hre : (∫ s : ℝ, sechKernel (1 / 2) (((u : ℂ) + d * I) - s) * sraGauss b s).re
      = ∫ s : ℝ, (sechKernel (1 / 2) (((u : ℂ) + d * I) - s) * sraGauss b s).re := by
    exact (integral_re hint).symm
  rw [hre]
  have hpos : ∀ s : ℝ, 0 < (sechKernel (1 / 2) (((u : ℂ) + d * I) - s) * sraGauss b s).re := by
    intro s
    rw [sraGauss_ofReal, Complex.re_mul_ofReal, sechKernel_shift_sub]
    exact mul_pos (re_sechKernel_shift_pos (by norm_num) _ hd) (by positivity)
  have hint' : Integrable (fun s : ℝ => (sechKernel (1 / 2) (((u : ℂ) + d * I) - s) * sraGauss b s).re) :=
    hint.re
  rw [integral_pos_iff_support_of_nonneg (fun s => (hpos s).le) hint']
  have hsupp : Function.support
      (fun s : ℝ => (sechKernel (1 / 2) (((u : ℂ) + d * I) - s) * sraGauss b s).re) = univ := by
    ext s; simp only [Function.mem_support, mem_univ, iff_true]; exact (hpos s).ne'
  rw [hsupp, Real.volume_univ]
  exact ENNReal.zero_lt_top

/-- **Strip-only positivity of the doubly smoothed zero terms.** For every nontrivial zero `ρ`, every `b > 0`
and every real `u`, `Re (K_{1/2} ∗ G_b)(u − z_ρ) > 0`. This is Sra's Theorem 2.3(i) mechanism for the kernel
`K_{1/2} ∗ G_b` (`K = K_h ∗ ν` with `h = ½`, `ν = G_b`, Theorem 2.3(ii)), at half-variance `1/8 + b`. -/
theorem sechGauss_zero_term_pos {b : ℝ} (hb : 0 < b) (x : Index) (u : ℝ) :
    0 < (sechGauss b ((u : ℂ) - ordinate (canonical x))).re := by
  rw [sub_ordinate_eq]
  exact re_sechGauss_pos hb _ (abs_displacement_lt x)

/-! ## Part 4. Window rate, strip width and half-variance -/

/-- Both maps in question send a strip half-width `h` to `h²/2`: hp-proof's window rate `c` gives the strip
`√(2c)`, and Sra's termwise half-variance `w` needs `h ≤ √(2w)`. -/
theorem sqrt_two_mul_half_sq {h : ℝ} (hh : 0 ≤ h) : Real.sqrt (2 * (h ^ 2 / 2)) = h := by
  rw [show 2 * (h ^ 2 / 2) = h ^ 2 by ring, Real.sqrt_sq hh]

/-- `c = 1/8` is the window rate of the trivial strip `|Re ρ − ½| ≤ ½`. -/
theorem sqrt_two_mul_one_eighth : Real.sqrt (2 * (1 / 8)) = 1 / 2 := by
  rw [show (1 / 8 : ℝ) = (1 / 2) ^ 2 / 2 by norm_num, sqrt_two_mul_half_sq (by norm_num)]

/-- `c = π²/288` corresponds to the strip half-width `π/12`. -/
theorem sqrt_two_mul_pi_sq_div_288 : Real.sqrt (2 * (π ^ 2 / 288)) = π / 12 := by
  rw [show π ^ 2 / 288 = (π / 12) ^ 2 / 2 by ring, sqrt_two_mul_half_sq (by positivity)]

/-- **What a pointwise π²/288 would give.** A window rate `c = π²/288` at every centre `|α| ≥ ½` confines every
nontrivial zero to `|Re ρ − ½| ≤ π/12 ≈ 0.2618`, a zero-free vertical strip that is not known. Sra's π²/288 is a
statement about a cumulative sum over all zeros, and does not give this hypothesis. -/
theorem zeros_in_strip_of_window_rate_pi_sq_div_288
    (h : ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ∫ t : ℝ, ‖FleetHeadContour.Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
        * Real.exp (-(t - α) ^ 2 / (4 * b)) ≤ C * Real.exp ((π ^ 2 / 288) / b)) :
    ∀ x : Index, |(canonical x).re - 1 / 2| ≤ π / 12 := by
  have := FleetHeadContour.zeros_in_strip_of_window_rate (by positivity) h
  rwa [sqrt_two_mul_pi_sq_div_288] at this

/-! ## Part 5. Freitas's Li-type coefficients and the window rate -/

/-- **The geometry behind Freitas's criterion.** For `τ > 0` and `ρ ≠ τ`,
`‖ρ/(ρ − τ)‖ ≤ 1 ↔ Re ρ ≤ τ/2`. Freitas's `α_n(τ) = τ⁻¹ Σ_ρ [1 − (ρ/(ρ−τ))ⁿ]` is built from these powers. -/
theorem norm_div_sub_le_one_iff {τ : ℝ} (hτ : 0 < τ) {ρ : ℂ} (hρ : ρ ≠ τ) :
    ‖ρ / (ρ - τ)‖ ≤ 1 ↔ ρ.re ≤ τ / 2 := by
  have hne : ρ - τ ≠ 0 := sub_ne_zero.2 hρ
  have hpos : 0 < ‖ρ - τ‖ := norm_pos_iff.2 hne
  rw [norm_div, div_le_one hpos, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Window rate ⇒ every Freitas term is in the closed unit disk.** If the window grows at most like
`C e^{c/b}` at every centre `|α| ≥ ½`, then with `τ = 1 + 2√(2c)` every nontrivial zero satisfies
`‖(ρ/(ρ − τ))ⁿ‖ ≤ 1` for all `n`: the half-plane `Re s > τ/2` of Freitas's Theorem 1 is zero-free. -/
theorem freitas_terms_le_one_of_window_rate {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ∫ t : ℝ, ‖FleetHeadContour.Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
        * Real.exp (-(t - α) ^ 2 / (4 * b)) ≤ C * Real.exp (c / b))
    (x : Index) (n : ℕ) :
    ‖(canonical x / (canonical x - ((1 + 2 * Real.sqrt (2 * c) : ℝ) : ℂ))) ^ n‖ ≤ 1 := by
  have hs := FleetHeadContour.zeros_in_strip_of_window_rate hc h x
  have hsq := Real.sqrt_nonneg (2 * c)
  have hτ : (0 : ℝ) < 1 + 2 * Real.sqrt (2 * c) := by linarith
  have hlt1 := ZetaStrip.re_lt_one_of_isNontrivialZero x.1.2
  have hρ : canonical x ≠ ((1 + 2 * Real.sqrt (2 * c) : ℝ) : ℂ) := by
    intro he
    have := congrArg Complex.re he
    simp only [ofReal_re] at this
    simp only [canonical] at this hlt1
    linarith
  have hd : ‖canonical x / (canonical x - ((1 + 2 * Real.sqrt (2 * c) : ℝ) : ℂ))‖ ≤ 1 := by
    rw [norm_div_sub_le_one_iff hτ hρ]
    have := (abs_le.1 hs).2
    linarith
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hd

/-! ## Part 6. Sra's heat sum is the centre-zero slice of hp-proof's zero trace -/

/-- `gaussHat b α z = √(π/b) e^{−t (z − α)²}` with `t = 1/(4b)`: the zero-trace term at centre `α` is the heat
term of `z − α`. -/
theorem gaussHat_eq_heat {b : ℝ} (hb : 0 < b) (α : ℝ) (z : ℂ) :
    gaussHat b α z = (Real.sqrt (π / b) : ℂ) * Complex.exp (-((1 / (4 * b) : ℝ) : ℂ) * (z - α) ^ 2) := by
  rw [gaussHat_eq hb]
  congr 2
  push_cast
  ring

/-- **hp-proof's Gaussian zero trace at `α = 0` is Sra's heat sum.** Summed over all nontrivial zeros (with
multiplicity), `Σ ĝ_{b,0}(z_ρ) = √(π/b) Σ e^{−t z_ρ²}` with `t = 1/(4b)`; Sra's `H(t)` is the same sum over the
zeros with `γ > 0`. -/
theorem zeroTrace_zero_eq_heat {b : ℝ} (hb : 0 < b) :
    ∑' x : Index, gaussHat b 0 (ordinate (canonical x))
      = (Real.sqrt (π / b) : ℂ)
        * ∑' x : Index, Complex.exp (-((1 / (4 * b) : ℝ) : ℂ) * (ordinate (canonical x)) ^ 2) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [gaussHat_eq_heat hb]
  push_cast
  ring_nf

/-! ## Part 7. The α-averaged zero trace: contour identity and unconditional positivity -/

/-- **Horizontal line shift.** If `f` is holomorphic on the closed strip between `Im = 0` and `Im = y`, integrable
on both boundary lines, and its vertical side integrals vanish at `±∞`, the two line integrals agree. -/
theorem integral_line_shift {f : ℂ → ℂ} {y : ℝ}
    (hd : DifferentiableOn ℂ f {z : ℂ | z.im ∈ [[0, y]]})
    (h0 : Integrable (fun x : ℝ => f (x : ℂ)))
    (hy : Integrable (fun x : ℝ => f ((x : ℂ) + y * I)))
    (hR : Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..y, f ((R : ℂ) + t * I)) atTop (𝓝 0))
    (hL : Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..y, f (((-R : ℝ) : ℂ) + t * I)) atTop (𝓝 0)) :
    ∫ x : ℝ, f (x : ℂ) = ∫ x : ℝ, f ((x : ℂ) + y * I) := by
  have hrect : ∀ R : ℝ, (∫ x in (-R)..R, f (x : ℂ)) - (∫ x in (-R)..R, f ((x : ℂ) + y * I))
      + I * (∫ t in (0 : ℝ)..y, f ((R : ℂ) + t * I))
      - I * (∫ t in (0 : ℝ)..y, f (((-R : ℝ) : ℂ) + t * I)) = 0 := by
    intro R
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      (((-R : ℝ) : ℂ) + (0 : ℝ) * I) ((R : ℂ) + y * I) (hd.mono ?_)
    · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
        add_zero, add_im, mul_im, zero_add, zero_mul, smul_eq_mul, ofReal_zero] at h
      simpa using h
    · intro z hz
      simp only [mem_reProdIm] at hz
      simp only [mem_ofPred_eq]
      simpa using hz.2
  have h1 := intervalIntegral_tendsto_integral h0 tendsto_neg_atTop_atBot tendsto_id
  have h2 := intervalIntegral_tendsto_integral hy tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((h1.sub h2).add (hR.const_mul I)).sub (hL.const_mul I)
  have hlim' : Tendsto (fun R : ℝ => (∫ x in (-R)..R, f (x : ℂ)) - (∫ x in (-R)..R, f ((x : ℂ) + y * I))
      + I * (∫ t in (0 : ℝ)..y, f ((R : ℂ) + t * I))
      - I * (∫ t in (0 : ℝ)..y, f (((-R : ℝ) : ℂ) + t * I))) atTop (𝓝 0) := by
    simp only [hrect]; exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hlim hlim'
  simp only [mul_zero, sub_zero, add_zero] at heq
  exact sub_eq_zero.1 heq



lemma cos_pi_le_of_abs_le {η t : ℝ} (ht : |t| ≤ |η|) (hη : |η| < 1 / 2) :
    Real.cos (π * η) ≤ Real.cos (π * t) := by
  rw [← Real.cos_abs (π * η), ← Real.cos_abs (π * t), abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  exact mul_le_mul_of_nonneg_left ht Real.pi_pos.le

lemma cos_pi_pos {η : ℝ} (hη : |η| < 1 / 2) : 0 < Real.cos (π * η) := by
  apply Real.cos_pos_of_mem_Ioo
  have h := abs_lt.1 hη
  constructor <;> nlinarith [Real.pi_pos]

lemma norm_sechKernel_half_le {η : ℝ} (hη : |η| < 1 / 2) (x : ℝ) {t : ℝ} (ht : |t| ≤ |η|) :
    ‖sechKernel (1 / 2) ((x : ℂ) + t * I)‖ ≤ 1 / Real.cos (π * η) := by
  have h := norm_sechKernel_shift_le (a := 1 / 2) (by norm_num) x (lt_of_le_of_lt ht hη)
  have e : 1 / (2 * (1 / 2 : ℝ)) / Real.cos (π * t / (2 * (1 / 2))) = 1 / Real.cos (π * t) := by
    norm_num
  rw [e] at h
  exact h.trans (one_div_le_one_div_of_le (cos_pi_pos hη) (cos_pi_le_of_abs_le ht hη))

lemma norm_sraGauss_ofReal {σ : ℝ} (s : ℝ) :
    ‖sraGauss σ (s : ℂ)‖ = (1 / Real.sqrt (4 * π * σ)) * Real.exp (-s ^ 2 / (4 * σ)) := by
  rw [sraGauss_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma integrable_norm_sraGauss {b : ℝ} (hb : 0 < b) :
    Integrable (fun s : ℝ => ‖sraGauss b (s : ℂ)‖) := by
  simp_rw [norm_sraGauss_ofReal]
  apply Integrable.const_mul
  have h := integrable_exp_neg_mul_sq (b := 1 / (4 * b)) (by positivity)
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only
  congr 1
  ring

lemma norm_sraGauss_shift_le {b : ℝ} (hb : 0 < b) (x : ℝ) {y Y : ℝ} (hy : |y| ≤ Y) :
    ‖sraGauss b ((x : ℂ) + y * I)‖ ≤ ‖sraGauss b x‖ * Real.exp (Y ^ 2 / (4 * b)) := by
  rw [norm_sraGauss_shift hb]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.2
  apply div_le_div_of_nonneg_right _ (by positivity)
  have := sq_le_sq' (abs_le.1 hy).1 (abs_le.1 hy).2
  exact this

lemma tendsto_norm_sraGauss {b : ℝ} (hb : 0 < b) :
    Tendsto (fun R : ℝ => ‖sraGauss b (R : ℂ)‖) atTop (𝓝 0) := by
  simp_rw [norm_sraGauss_ofReal]
  rw [show (0 : ℝ) = (1 / Real.sqrt (4 * π * b)) * 0 by ring]
  apply Tendsto.const_mul
  apply Real.tendsto_exp_atBot.comp
  have h : Tendsto (fun R : ℝ => R ^ 2 / (4 * b)) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const (by positivity)
  have := tendsto_neg_atTop_atBot.comp h
  refine this.congr fun R => ?_
  simp only [Function.comp]
  ring

/-- **The α-average of hp-proof's Gaussian zero-trace term is the doubly smoothed kernel.** For `b > 0` and any
complex `z` with `|Im z| < ½`,
`∫ K_{1/2}(α − α') ĝ_{b,α'}(z) dα' = 2π (K_{1/2} ∗ G_b)(α − z)`. (Real translation plus a horizontal contour
shift through the strip `|Im| < ½`, where `K_{1/2}` is holomorphic.) -/
theorem integral_sech_gaussHat {b : ℝ} (hb : 0 < b) (α : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    ∫ α' : ℝ, sechKernel (1 / 2) ((α : ℂ) - α') * gaussHat b α' z
      = 2 * π * sechGauss b ((α : ℂ) - z) := by
  set γ := z.re
  set η := z.im
  set w0 : ℝ := α - γ
  have hzeq : z = (γ : ℂ) + η * I := (Complex.re_add_im z).symm
  set φ : ℂ → ℂ := fun ζ => sechKernel (1 / 2) ((w0 : ℂ) - ζ) * sraGauss b (ζ - η * I) with hφ
  -- step 1: pull out 2π and translate by γ
  have h1 : ∫ α' : ℝ, sechKernel (1 / 2) ((α : ℂ) - α') * gaussHat b α' z
      = 2 * π * ∫ s : ℝ, φ (s : ℂ) := by
    have e : ∀ α' : ℝ, sechKernel (1 / 2) ((α : ℂ) - α') * gaussHat b α' z
        = 2 * π * φ (((α' - γ : ℝ)) : ℂ) := by
      intro α'
      rw [gaussHat_eq_sraGauss hb, hφ]
      simp only
      have e1 : (α : ℂ) - α' = (w0 : ℂ) - ((α' - γ : ℝ) : ℂ) := by simp [w0]
      have e2 : (α' : ℂ) - z = ((α' - γ : ℝ) : ℂ) - η * I := by rw [hzeq]; push_cast; ring
      rw [e1, e2]; ring
    simp_rw [e]
    rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun s : ℝ => φ (s : ℂ)) γ
  -- step 2: the line shift
  have hcosh : ∀ ζ : ℂ, |ζ.im| ≤ |η| → Complex.cosh (π * ((w0 : ℂ) - ζ) / (2 * (1 / 2 : ℝ))) ≠ 0 := by
    intro ζ hζ h
    have hp := re_sechKernel_shift_pos (a := 1 / 2) (by norm_num) (w0 - ζ.re) (d := -ζ.im)
      (by rw [abs_neg]; exact lt_of_le_of_lt hζ hz)
    have e : ((w0 - ζ.re : ℝ) : ℂ) + ((-ζ.im : ℝ) : ℂ) * I = (w0 : ℂ) - ζ := by
      conv_rhs => rw [← Complex.re_add_im ζ]
      push_cast; ring
    rw [e] at hp
    unfold sechKernel at hp
    rw [h, div_zero, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  have hdiff : DifferentiableOn ℂ φ {ζ : ℂ | ζ.im ∈ [[0, η]]} := by
    intro ζ hζ
    have hζ' : |ζ.im| ≤ |η| := by
      simp only [mem_ofPred_eq, Set.mem_uIcc] at hζ
      rcases hζ with h | h <;> rw [abs_le] <;> constructor <;>
        cases abs_cases η <;> linarith [h.1, h.2]
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.mul
    · unfold sechKernel
      have hg : DifferentiableAt ℂ (fun ζ : ℂ => Complex.cosh (↑π * (↑w0 - ζ) / (2 * ((1 / 2 : ℝ) : ℂ)))) ζ := by
        fun_prop
      exact (differentiableAt_const _).div hg (hcosh ζ hζ')
    · unfold sraGauss
      fun_prop
  have hint0 : Integrable (fun x : ℝ => φ (x : ℂ)) := by
    have hg : Integrable (fun x : ℝ => sraGauss b ((x : ℂ) - η * I)) := by
      refine Integrable.mono' ((integrable_norm_sraGauss hb).mul_const (Real.exp (|η| ^ 2 / (4 * b)))) ?_
        (Eventually.of_forall fun x => ?_)
      · exact (by unfold sraGauss; fun_prop : Continuous fun x : ℝ => sraGauss b ((x : ℂ) - η * I)).aestronglyMeasurable
      · have e : (x : ℂ) - η * I = (x : ℂ) + ((-η : ℝ) : ℂ) * I := by push_cast; ring
        rw [e]
        exact norm_sraGauss_shift_le hb x (by rw [abs_neg])
    refine hg.bdd_mul (c := 1 / Real.cos (π * η)) ?_ (Eventually.of_forall fun x => ?_)
    · have : Continuous (fun x : ℝ => sechKernel (1 / 2) ((w0 : ℂ) - x)) := by
        unfold sechKernel
        apply Continuous.div continuous_const (by fun_prop)
        intro x; exact hcosh x (by simp)
      exact this.aestronglyMeasurable
    · have e : (w0 : ℂ) - (x : ℂ) = ((w0 - x : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by push_cast; ring
      rw [e]
      exact norm_sechKernel_half_le hz _ (by simp)
  have hlineη : ∀ x : ℝ, φ ((x : ℂ) + η * I)
      = sechKernel (1 / 2) ((((w0 : ℂ) + ((-η : ℝ) : ℂ) * I)) - x) * sraGauss b x := by
    intro x
    simp only [hφ]
    congr 2 <;> push_cast <;> ring
  have hintη : Integrable (fun x : ℝ => φ ((x : ℂ) + η * I)) := by
    simp_rw [hlineη]
    exact integrable_sechGauss_integrand hb w0 (by rw [abs_neg]; exact hz)
  have hvert : ∀ R : ℝ, ‖∫ t in (0 : ℝ)..η, φ ((R : ℂ) + t * I)‖
      ≤ (1 / Real.cos (π * η)) * (‖sraGauss b (R : ℂ)‖ * Real.exp ((2 * |η|) ^ 2 / (4 * b))) * |η - 0| := by
    intro R
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have ht' : |t| ≤ |η| := by
      rw [Set.uIoc] at ht
      rcases ht with ⟨h1, h2⟩
      rcases le_total 0 η with h | h
      · simp [h] at h1 h2; rw [abs_le]; constructor <;> cases abs_cases η <;> linarith
      · simp [h] at h1 h2; rw [abs_le]; constructor <;> cases abs_cases η <;> linarith
    simp only [hφ, norm_mul]
    apply mul_le_mul _ _ (norm_nonneg _) (by have := cos_pi_pos hz; positivity)
    · have e : (w0 : ℂ) - ((R : ℂ) + t * I) = ((w0 - R : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
      rw [e]
      exact norm_sechKernel_half_le hz _ (by rwa [abs_neg])
    · have e : (R : ℂ) + t * I - η * I = (R : ℂ) + ((t - η : ℝ) : ℂ) * I := by push_cast; ring
      rw [e]
      apply norm_sraGauss_shift_le hb
      calc |t - η| ≤ |t| + |η| := abs_sub _ _
        _ ≤ 2 * |η| := by linarith
  have hvert' : ∀ R : ℝ, ‖∫ t in (0 : ℝ)..η, φ (((-R : ℝ) : ℂ) + t * I)‖
      ≤ (1 / Real.cos (π * η)) * (‖sraGauss b (R : ℂ)‖ * Real.exp ((2 * |η|) ^ 2 / (4 * b))) * |η - 0| := by
    intro R
    have := hvert (-R)
    have e : ‖sraGauss b (((-R : ℝ)) : ℂ)‖ = ‖sraGauss b (R : ℂ)‖ := by
      rw [norm_sraGauss_ofReal, norm_sraGauss_ofReal, neg_sq]
    rwa [e] at this
  have hM : Tendsto (fun R : ℝ =>
      (1 / Real.cos (π * η)) * (‖sraGauss b (R : ℂ)‖ * Real.exp ((2 * |η|) ^ 2 / (4 * b))) * |η - 0|)
      atTop (𝓝 0) := by
    have := (((tendsto_norm_sraGauss hb).mul_const (Real.exp ((2 * |η|) ^ 2 / (4 * b)))).const_mul
      (1 / Real.cos (π * η))).mul_const |η - 0|
    simpa using this
  have hR := squeeze_zero_norm hvert hM
  have hL := squeeze_zero_norm hvert' hM
  have hshift := integral_line_shift hdiff hint0 hintη hR hL
  rw [h1, hshift]
  congr 1
  unfold sechGauss
  simp_rw [hlineη]
  congr 1
  · rw [hzeq]; push_cast; simp [w0]; ring_nf


/-- **Per-zero α-averaged positivity.** For every nontrivial zero `ρ`, every `b > 0` and every centre `α`, the
zero-trace term `ĝ_{b,α'}(z_ρ)` averaged over `α'` against the strip Poisson kernel `K_{1/2}(α − α')` has positive
real part. -/
theorem re_integral_sech_gaussHat_pos {b : ℝ} (hb : 0 < b) (α : ℝ) (x : Index) :
    0 < (∫ α' : ℝ, sechKernel (1 / 2) ((α : ℂ) - α') * gaussHat b α' (ordinate (canonical x))).re := by
  have him : |(ordinate (canonical x)).im| < 1 / 2 := by
    rw [ordinate_im, abs_sub_comm]; exact abs_displacement_lt x
  rw [integral_sech_gaussHat hb α him]
  have e : (2 * (π : ℂ) * sechGauss b ((α : ℂ) - ordinate (canonical x))).re
      = 2 * π * (sechGauss b ((α : ℂ) - ordinate (canonical x))).re := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  rw [e]
  exact mul_pos (by positivity) (sechGauss_zero_term_pos hb x α)

/-! ### Summing over the zeros -/

lemma exp_abs_le_two_cosh (u : ℝ) : Real.exp |u| ≤ 2 * Real.cosh u := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have := Real.exp_pos (-|u|)
  linarith

lemma norm_sechKernel_half_real (r : ℝ) :
    ‖sechKernel (1 / 2) (r : ℂ)‖ ≤ 2 * Real.exp (-(π * |r|)) := by
  have e : sechKernel (1 / 2) (r : ℂ) = ((1 / Real.cosh (π * r) : ℝ) : ℂ) := by
    unfold sechKernel
    rw [show (π : ℂ) * (r : ℂ) / (2 * ((1 / 2 : ℝ) : ℂ)) = ((π * r : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cosh]
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by have := Real.cosh_pos (π * r); positivity)]
  have hc := exp_abs_le_two_cosh (π * r)
  have hcp := Real.cosh_pos (π * r)
  rw [abs_mul, abs_of_pos Real.pi_pos] at hc
  rw [Real.exp_neg, div_le_iff₀ hcp]
  have hep := Real.exp_pos (π * |r|)
  rw [show 2 * (Real.exp (π * |r|))⁻¹ * Real.cosh (π * r) = 2 * Real.cosh (π * r) / Real.exp (π * |r|) by
    field_simp]
  rw [le_div_iff₀ hep]
  linarith

lemma norm_gaussHat_le_strip {b : ℝ} (hb : 0 < b) (α' : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖gaussHat b α' z‖ ≤ Real.sqrt (π / b) * Real.exp (1 / (16 * b)) * Real.exp (-(z.re - α') ^ 2 / (4 * b)) := by
  rw [norm_gaussHat hb, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.2
  have h2 : z.im ^ 2 ≤ 1 / 4 := by
    have := sq_le_sq' (abs_le.1 hz).1 (abs_le.1 hz).2; nlinarith
  have e : 1 / (16 * b) + -(z.re - α') ^ 2 / (4 * b) = (1 / 4 - (z.re - α') ^ 2) / (4 * b) := by
    field_simp; ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The pointwise exponent inequality `π u + v²/(4b) ≥ π D − 2bπ² + v²/(8b)` with `D ≤ u + v`. -/
lemma exponent_ineq {b : ℝ} (hb : 0 < b) (α α' γ : ℝ) :
    -(π * |α - α'|) + -(γ - α') ^ 2 / (4 * b)
      ≤ 2 * b * π ^ 2 + -(π * |γ - α|) + -(γ - α') ^ 2 / (8 * b) := by
  have htri : |γ - α| ≤ |α - α'| + |γ - α'| := by
    calc |γ - α| = |(γ - α') + (α' - α)| := by ring_nf
      _ ≤ |γ - α'| + |α' - α| := abs_add_le _ _
      _ = |α - α'| + |γ - α'| := by rw [abs_sub_comm α' α]; ring
  set v := |γ - α'|
  have hv : (γ - α') ^ 2 = v ^ 2 := (sq_abs _).symm
  rw [hv]
  have key : π * v ≤ 2 * b * π ^ 2 + v ^ 2 / (8 * b) := by
    have h := sq_nonneg (v - 4 * b * π)
    rw [show 2 * b * π ^ 2 + v ^ 2 / (8 * b) = (16 * b ^ 2 * π ^ 2 + v ^ 2) / (8 * b) by field_simp; ring,
      le_div_iff₀ (by positivity)]
    nlinarith
  have e1 : -(v ^ 2) / (4 * b) = -(v ^ 2 / (8 * b)) - v ^ 2 / (8 * b) := by field_simp; ring
  have e2 : -(v ^ 2) / (8 * b) = -(v ^ 2 / (8 * b)) := by ring
  rw [e1, e2]
  nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left htri Real.pi_pos.le]

lemma integrand_bound {b : ℝ} (hb : 0 < b) (α α' : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖sechKernel (1 / 2) ((α : ℂ) - α') * gaussHat b α' z‖
      ≤ (2 * Real.sqrt (π / b) * Real.exp (1 / (16 * b)) * Real.exp (2 * b * π ^ 2))
        * Real.exp (-(π * |z.re - α|)) * Real.exp (-(z.re - α') ^ 2 / (8 * b)) := by
  rw [norm_mul]
  have hK := norm_sechKernel_half_real (α - α')
  rw [show ((α - α' : ℝ) : ℂ) = (α : ℂ) - α' by push_cast; ring] at hK
  have hG := norm_gaussHat_le_strip hb α' hz
  calc ‖sechKernel (1 / 2) ((α : ℂ) - α')‖ * ‖gaussHat b α' z‖
      ≤ (2 * Real.exp (-(π * |α - α'|)))
        * (Real.sqrt (π / b) * Real.exp (1 / (16 * b)) * Real.exp (-(z.re - α') ^ 2 / (4 * b))) :=
        mul_le_mul hK hG (norm_nonneg _) (by positivity)
    _ = (2 * Real.sqrt (π / b) * Real.exp (1 / (16 * b)))
        * Real.exp (-(π * |α - α'|) + -(z.re - α') ^ 2 / (4 * b)) := by
        rw [Real.exp_add]; ring
    _ ≤ (2 * Real.sqrt (π / b) * Real.exp (1 / (16 * b)))
        * Real.exp (2 * b * π ^ 2 + -(π * |z.re - α|) + -(z.re - α') ^ 2 / (8 * b)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.2 (exponent_ineq hb α α' z.re)
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

lemma integrable_gauss_shift {b : ℝ} (hb : 0 < b) (γ : ℝ) :
    Integrable (fun α' : ℝ => Real.exp (-(γ - α') ^ 2 / (8 * b))) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / (8 * b)) (by positivity)).comp_sub_right γ
  refine h.congr (Eventually.of_forall fun α' => ?_)
  ring_nf

lemma integral_gauss_shift {b : ℝ} (hb : 0 < b) (γ : ℝ) :
    ∫ α' : ℝ, Real.exp (-(γ - α') ^ 2 / (8 * b)) = Real.sqrt (8 * π * b) := by
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun x : ℝ => Real.exp (-(1 / (8 * b)) * x ^ 2)) γ
  have h2 := integral_gaussian (1 / (8 * b))
  have e : ∀ α' : ℝ, Real.exp (-(γ - α') ^ 2 / (8 * b)) = Real.exp (-(1 / (8 * b)) * (α' - γ) ^ 2) := by
    intro α'; congr 1; field_simp; ring
  simp_rw [e]
  rw [h, h2]
  congr 1
  field_simp

lemma continuous_sech_gaussHat {b : ℝ} (hb : 0 < b) (α : ℝ) (z : ℂ) :
    Continuous (fun α' : ℝ => sechKernel (1 / 2) ((α : ℂ) - α') * gaussHat b α' z) := by
  have hK : Continuous (fun α' : ℝ => sechKernel (1 / 2) ((α : ℂ) - α')) := by
    unfold sechKernel
    apply Continuous.div continuous_const (by fun_prop)
    intro α' h
    have e : (π : ℂ) * ((α : ℂ) - α') / (2 * ((1 / 2 : ℝ) : ℂ)) = ((π * (α - α') : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, ← Complex.ofReal_cosh] at h
    exact (Real.cosh_pos _).ne' (by exact_mod_cast h)
  have hG : Continuous (fun α' : ℝ => gaussHat b α' z) := by
    simp_rw [gaussHat_eq hb]
    fun_prop
  exact hK.mul hG

/-- **The sech-averaged Gaussian zero trace.** For `b > 0` and every centre `α`, the zero trace
`R_b(α') = Σ_ρ ĝ_{b,α'}(z_ρ)` averaged against `K_{1/2}(α − α')` is the absolutely convergent sum of the
doubly smoothed zero terms: `∫ K_{1/2}(α − α') R_b(α') dα' = Σ_ρ 2π (K_{1/2} ∗ G_b)(α − z_ρ)`. -/
theorem hasSum_sech_zeroTrace {b : ℝ} (hb : 0 < b) (α : ℝ) :
    HasSum (fun x : Index => 2 * π * sechGauss b ((α : ℂ) - ordinate (canonical x)))
      (∫ α' : ℝ, sechKernel (1 / 2) ((α : ℂ) - α') * ∑' x : Index, gaussHat b α' (ordinate (canonical x))) := by
  set F : Index → ℝ → ℂ := fun x α' => sechKernel (1 / 2) ((α : ℂ) - α') * gaussHat b α' (ordinate (canonical x))
    with hF
  set A := 2 * Real.sqrt (π / b) * Real.exp (1 / (16 * b)) * Real.exp (2 * b * π ^ 2) with hA
  have hzim : ∀ x : Index, |(ordinate (canonical x)).im| ≤ 1 / 2 := by
    intro x; rw [ordinate_im, abs_sub_comm]; exact (abs_displacement_lt x).le
  have hbound : ∀ x : Index, ∀ α' : ℝ, ‖F x α'‖
      ≤ A * Real.exp (-(π * |(ordinate (canonical x)).re - α|))
        * Real.exp (-((ordinate (canonical x)).re - α') ^ 2 / (8 * b)) :=
    fun x α' => integrand_bound hb α α' (hzim x)
  have hint : ∀ x : Index, Integrable (F x) := by
    intro x
    refine Integrable.mono' ((integrable_gauss_shift hb (ordinate (canonical x)).re).const_mul
      (A * Real.exp (-(π * |(ordinate (canonical x)).re - α|))))
      (continuous_sech_gaussHat hb α _).aestronglyMeasurable (Eventually.of_forall fun α' => ?_)
    exact hbound x α'
  have hintnorm : ∀ x : Index, ∫ α', ‖F x α'‖
      ≤ A * Real.exp (-(π * |(ordinate (canonical x)).re - α|)) * Real.sqrt (8 * π * b) := by
    intro x
    calc ∫ α', ‖F x α'‖
        ≤ ∫ α', A * Real.exp (-(π * |(ordinate (canonical x)).re - α|))
            * Real.exp (-((ordinate (canonical x)).re - α') ^ 2 / (8 * b)) :=
          MeasureTheory.integral_mono (f := fun α' => ‖F x α'‖)
            (g := fun α' => A * Real.exp (-(π * |(ordinate (canonical x)).re - α|))
              * Real.exp (-((ordinate (canonical x)).re - α') ^ 2 / (8 * b)))
            (hint x).norm ((integrable_gauss_shift hb (ordinate (canonical x)).re).const_mul _)
            (fun α' => hbound x α')
      _ = _ := by rw [integral_const_mul, integral_gauss_shift hb]
  -- `e^{−πD} ≤ (4/π² + 2α²)/γ²`
  have hdecay : ∀ γ : ℝ, γ ≠ 0 →
      Real.exp (-(π * |γ - α|)) ≤ (4 / π ^ 2 + 2 * α ^ 2) * (1 / γ ^ 2) := by
    intro γ hγ
    set D := |γ - α|
    have hD : 0 ≤ D := abs_nonneg _
    have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg Real.pi_pos.le hD)
    have hE := Real.exp_pos (π * D)
    have hγ2 : γ ^ 2 ≤ 2 * D ^ 2 + 2 * α ^ 2 := by
      have : γ ^ 2 = ((γ - α) + α) ^ 2 := by ring
      rw [this, show D ^ 2 = (γ - α) ^ 2 from sq_abs _]
      nlinarith [sq_nonneg (γ - α - α)]
    have hγp : 0 < γ ^ 2 := by positivity
    rw [Real.exp_neg, mul_one_div, le_div_iff₀ hγp, inv_mul_eq_div, div_le_iff₀ hE]
    have hpi := Real.pi_pos
    have h1 : 2 * D ^ 2 ≤ 4 / π ^ 2 * Real.exp (π * D) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [mul_pos hpi hpi]
    have h2 : 2 * α ^ 2 ≤ 2 * α ^ 2 * Real.exp (π * D) := by
      have : 1 ≤ Real.exp (π * D) := Real.one_le_exp (by positivity)
      nlinarith [sq_nonneg α]
    nlinarith
  have hsum : Summable (fun x : Index => ∫ α', ‖F x α'‖) := by
    have hg := (summable_inv_sq_im multEnum_canonical).mul_left
      (A * Real.sqrt (8 * π * b) * (4 / π ^ 2 + 2 * α ^ 2))
    refine Summable.of_norm_bounded_eventually hg ?_
    rw [Filter.eventually_cofinite]
    refine (multEnum_canonical.finite 0).subset ?_
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    by_contra h0
    apply hx
    have hγ : (canonical x).im ≠ 0 := by
      intro h; apply h0; simp [h]
    have hre : (ordinate (canonical x)).re = (canonical x).im := by simp [ordinate]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc ∫ α', ‖F x α'‖
        ≤ A * Real.exp (-(π * |(ordinate (canonical x)).re - α|)) * Real.sqrt (8 * π * b) := hintnorm x
      _ ≤ A * ((4 / π ^ 2 + 2 * α ^ 2) * (1 / (canonical x).im ^ 2)) * Real.sqrt (8 * π * b) := by
          rw [hre]
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left (hdecay _ hγ) (by positivity)
      _ = _ := by ring
  have hHas := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ x : Index, ∫ α', F x α' = 2 * π * sechGauss b ((α : ℂ) - ordinate (canonical x)) := by
    intro x
    have him : |(ordinate (canonical x)).im| < 1 / 2 := by
      rw [ordinate_im, abs_sub_comm]; exact abs_displacement_lt x
    exact integral_sech_gaussHat hb α him
  simp_rw [hval] at hHas
  convert hHas using 1
  congr 1
  funext α'
  rw [hF]
  simp only
  rw [tsum_mul_left]

/-- **Unconditional averaged positivity of the Gaussian zero trace (strip-only level).** For every `b > 0` and
every centre `α`, `Re ∫ K_{1/2}(α − α') R_b(α') dα' ≥ 0`, and `> 0` as soon as one nontrivial zero exists. -/
theorem re_sech_zeroTrace_nonneg {b : ℝ} (hb : 0 < b) (α : ℝ) :
    0 ≤ (∫ α' : ℝ, sechKernel (1 / 2) ((α : ℂ) - α')
      * ∑' x : Index, gaussHat b α' (ordinate (canonical x))).re := by
  have h := Complex.hasSum_re (hasSum_sech_zeroTrace hb α)
  refine h.nonneg fun x => ?_
  have e : (2 * (π : ℂ) * sechGauss b ((α : ℂ) - ordinate (canonical x))).re
      = 2 * π * (sechGauss b ((α : ℂ) - ordinate (canonical x))).re := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  rw [e]
  exact (mul_pos (by positivity) (sechGauss_zero_term_pos hb x α)).le

theorem re_sech_zeroTrace_pos {b : ℝ} (hb : 0 < b) (α : ℝ) (x₀ : Index) :
    0 < (∫ α' : ℝ, sechKernel (1 / 2) ((α : ℂ) - α')
      * ∑' x : Index, gaussHat b α' (ordinate (canonical x))).re := by
  have h := Complex.hasSum_re (hasSum_sech_zeroTrace hb α)
  have hpos : ∀ x : Index, 0 < (2 * (π : ℂ) * sechGauss b ((α : ℂ) - ordinate (canonical x))).re := by
    intro x
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    exact mul_pos (by positivity) (sechGauss_zero_term_pos hb x α)
  rw [← h.tsum_eq]
  exact h.summable.tsum_pos (fun x => (hpos x).le) x₀ (hpos x₀)

end FleetSraSmoothing
