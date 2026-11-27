import Mathlib

/-!
# An explicit upper bound for the sign uncertainty constant

The `+1` sign uncertainty problem of Bourgain, Clozel and Kahane in dimension one, in the
normalisation of problem 11 of the AlphaEvolve repository of problems: for even `f ∈ L¹(ℝ)`
with `f(0) < 0` and `f̂(0) < 0`, where `f̂(ξ) = ∫ f(x) e^{-2πixξ} dx`, let
`A(g) = inf {r > 0 : g(x) ≥ 0 for all |x| ≥ r}`; the constant is the largest `C` with
`A(f) A(f̂) ≥ C`.

This file proves `signUncertaintyConstant ≤ (an explicit rational) / (2π)` by an explicit
function `f(x) = Q(2πx²) e^{-πx²}`, where `Q` is an explicit integer polynomial.

* `f̂ = f` is proved in general: every `q(2πx²) e^{-πx²}` with `q` in the span of the
  iterates `T^k 1` (`T` = four normalised raising operators `a† = 2πx - d/dx`) is fixed by
  the Fourier transform (`eig_hornerTP`).
* the sign conditions on `Q` are checked by kernel evaluation (`decide +kernel`) of exact
  natural-number certificates (Descartes-type leaves: all coefficients of `(1+z)^n p(1/(1+z))`
  nonnegative, and a nonnegative Taylor expansion for the tail), whose soundness is proved here
  (`leavesOK_pos`, `tail_pos`).

Polynomials are stored as pairs of natural-number coefficient lists `(P, N)` meaning `P - N`,
lowest degree first; this keeps every kernel computation in GMP-accelerated `Nat` arithmetic.
-/

namespace FleetSignUncertainty

open Complex MeasureTheory Real
open scoped FourierTransform

/-! ## Natural-number coefficient lists -/

/-- Horner evaluation of a natural-number coefficient list (lowest degree first). -/
def evalN {R : Type*} [CommSemiring R] : List ℕ → R → R
  | [], _ => 0
  | c :: cs, t => (c : R) + t * evalN cs t

def addN : List ℕ → List ℕ → List ℕ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addN p q

def scaleN (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: cs => (k * c) :: scaleN k cs

def derivAuxN : ℕ → List ℕ → List ℕ
  | _, [] => []
  | n, c :: cs => (n * c) :: derivAuxN (n + 1) cs

def derivN : List ℕ → List ℕ
  | [] => []
  | _ :: cs => derivAuxN 1 cs

section EvalN
variable {R : Type*} [CommSemiring R]

@[simp] theorem evalN_nil (t : R) : evalN [] t = 0 := rfl
@[simp] theorem evalN_cons (c : ℕ) (cs : List ℕ) (t : R) :
    evalN (c :: cs) t = (c : R) + t * evalN cs t := rfl

theorem evalN_addN (p q : List ℕ) (t : R) : evalN (addN p q) t = evalN p t + evalN q t := by
  induction p generalizing q with
  | nil => simp [addN]
  | cons a p ih =>
    cases q with
    | nil => simp [addN]
    | cons b q => simp [addN, ih]; ring

theorem evalN_scaleN (k : ℕ) (p : List ℕ) (t : R) : evalN (scaleN k p) t = k * evalN p t := by
  induction p with
  | nil => simp [scaleN]
  | cons a p ih => simp [scaleN, ih]; ring

end EvalN

theorem hasDerivAt_pow_mul_evalN (l : List ℕ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ (n + 1) * evalN l t) (t ^ n * evalN (derivAuxN (n + 1) l) t) t := by
  induction l generalizing n with
  | nil => simpa [derivAuxN] using hasDerivAt_const t (0 : ℝ)
  | cons c cs ih =>
    have h := ((hasDerivAt_pow (n + 1) t).const_mul (c : ℝ)).add (ih (n + 1))
    have hf : (fun t : ℝ => t ^ (n + 1) * evalN (c :: cs) t) =
        fun t : ℝ => (c : ℝ) * t ^ (n + 1) + t ^ (n + 1 + 1) * evalN cs t := by
      funext t; simp; ring
    rw [hf]
    convert h using 1
    simp [derivAuxN]; ring

theorem hasDerivAt_evalN (l : List ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => evalN l t) (evalN (derivN l) t) t := by
  cases l with
  | nil => simpa [derivN] using hasDerivAt_const t (0 : ℝ)
  | cons c cs =>
    have h := (hasDerivAt_pow_mul_evalN cs 0 t).const_add (c : ℝ)
    have hf : (fun t : ℝ => evalN (c :: cs) t) = fun t : ℝ => (c : ℝ) + t ^ (0 + 1) * evalN cs t := by
      funext t; simp
    rw [hf]; simpa [derivN] using h

/-! ## Signed polynomials as pairs `P - N` -/

/-- A pair `(P, N)` of coefficient lists, standing for the polynomial `P - N`. -/
abbrev NP := List ℕ × List ℕ

/-- Evaluation of the signed polynomial `P - N`. -/
def evalP {R : Type*} [CommRing R] (a : NP) (t : R) : R := evalN a.1 t - evalN a.2 t

def addP (a b : NP) : NP := (addN a.1 b.1, addN a.2 b.2)
def subP (a b : NP) : NP := (addN a.1 b.2, addN a.2 b.1)
def scaleP (k : ℕ) (a : NP) : NP := (scaleN k a.1, scaleN k a.2)
def mulXP (a : NP) : NP := (0 :: a.1, 0 :: a.2)
def derivP (a : NP) : NP := (derivN a.1, derivN a.2)

section EvalP
variable {R : Type*} [CommRing R]

theorem evalP_addP (a b : NP) (t : R) : evalP (addP a b) t = evalP a t + evalP b t := by
  simp [evalP, addP, evalN_addN]; ring

theorem evalP_subP (a b : NP) (t : R) : evalP (subP a b) t = evalP a t - evalP b t := by
  simp [evalP, subP, evalN_addN]; ring

theorem evalP_scaleP (k : ℕ) (a : NP) (t : R) : evalP (scaleP k a) t = k * evalP a t := by
  simp [evalP, scaleP, evalN_scaleN]; ring

theorem evalP_mulXP (a : NP) (t : R) : evalP (mulXP a) t = t * evalP a t := by
  simp [evalP, mulXP]; ring

end EvalP

theorem hasDerivAt_evalP (a : NP) (t : ℝ) :
    HasDerivAt (fun t : ℝ => evalP a t) (evalP (derivP a) t) t := by
  have h := (hasDerivAt_evalN a.1 t).sub (hasDerivAt_evalN a.2 t)
  exact h


/-! ## Gaussian times a polynomial in `t = 2πx²` -/

/-- The Gaussian `e^{-πx²}`, fixed by the Fourier transform. -/
noncomputable def gauss (x : ℝ) : ℝ := Real.exp (-π * x ^ 2)

/-- Even functions `q(2πx²) e^{-πx²}`. -/
noncomputable def phiE (l : NP) (x : ℝ) : ℝ := evalP l (2 * π * x ^ 2) * gauss x

/-- Odd functions `x q(2πx²) e^{-πx²}`. -/
noncomputable def phiO (l : NP) (x : ℝ) : ℝ := x * evalP l (2 * π * x ^ 2) * gauss x

theorem integrable_pow_mul_gauss (n : ℕ) : Integrable (fun x : ℝ => x ^ n * gauss x) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := π) Real.pi_pos (s := (n : ℝ))
    (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  simpa [gauss, Real.rpow_natCast] using h

theorem integrable_pow_mul_evalN_gauss (l : List ℕ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * evalN l (2 * π * x ^ 2) * gauss x) := by
  induction l generalizing n with
  | nil => simp
  | cons c cs ih =>
    have h := ((integrable_pow_mul_gauss n).const_mul (c : ℝ)).add ((ih (n + 2)).const_mul (2 * π))
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    show (c : ℝ) * (x ^ n * gauss x) + 2 * π * (x ^ (n + 2) * evalN cs (2 * π * x ^ 2) * gauss x) =
      x ^ n * evalN (c :: cs) (2 * π * x ^ 2) * gauss x
    rw [evalN_cons]; ring

theorem integrable_pow_mul_evalP_gauss (l : NP) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * evalP l (2 * π * x ^ 2) * gauss x) := by
  refine ((integrable_pow_mul_evalN_gauss l.1 n).sub (integrable_pow_mul_evalN_gauss l.2 n)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply, evalP]; ring

theorem integrable_phiE (l : NP) : Integrable (phiE l) := by
  have h := integrable_pow_mul_evalP_gauss l 0
  simp only [pow_zero, one_mul] at h
  exact h

theorem integrable_phiO (l : NP) : Integrable (phiO l) := by
  have h := integrable_pow_mul_evalP_gauss l 1
  simp only [pow_one] at h
  exact h

theorem integrable_x_mul_phiE (l : NP) : Integrable (fun x => x * phiE l x) := by
  refine (integrable_pow_mul_evalP_gauss l 1).congr (Filter.Eventually.of_forall fun x => ?_)
  simp [phiE]; ring

theorem integrable_x_mul_phiO (l : NP) : Integrable (fun x => x * phiO l x) := by
  refine (integrable_pow_mul_evalP_gauss l 2).congr (Filter.Eventually.of_forall fun x => ?_)
  simp [phiO]; ring

theorem hasDerivAt_gauss (x : ℝ) : HasDerivAt gauss (-2 * π * x * gauss x) x := by
  have h := ((hasDerivAt_pow 2 x).const_mul (-π)).exp
  have e : (-2 * π * x * gauss x) = Real.exp (-π * x ^ 2) * (-π * ((2 : ℕ) * x ^ (2 - 1))) := by
    simp only [gauss]; push_cast; ring
  rw [e]; exact h

theorem hasDerivAt_evalP_sq (l : NP) (x : ℝ) :
    HasDerivAt (fun x : ℝ => evalP l (2 * π * x ^ 2))
      (evalP (derivP l) (2 * π * x ^ 2) * (4 * π * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * π * x ^ 2) (4 * π * x) x := by
    convert (hasDerivAt_pow 2 x).const_mul (2 * π) using 1; push_cast; ring
  exact (hasDerivAt_evalP l (2 * π * x ^ 2)).comp x h1

/-- Even step: `d/dx (q(t) G) = -2πx (q - 2q')(t) G`. -/
theorem hasDerivAt_phiE (l : NP) (x : ℝ) :
    HasDerivAt (phiE l) (-2 * π * phiO (subP l (scaleP 2 (derivP l))) x) x := by
  have h := (hasDerivAt_evalP_sq l x).mul (hasDerivAt_gauss x)
  have e : -2 * π * phiO (subP l (scaleP 2 (derivP l))) x =
      evalP (derivP l) (2 * π * x ^ 2) * (4 * π * x) * gauss x +
        evalP l (2 * π * x ^ 2) * (-2 * π * x * gauss x) := by
    simp only [phiO, evalP_subP, evalP_scaleP]; push_cast; ring
  rw [e]; exact h

/-- Odd step: `d/dx (x r(t) G) = (r + 2t r' - t r)(t) G`. -/
theorem hasDerivAt_phiO (l : NP) (x : ℝ) :
    HasDerivAt (phiO l) (phiE (subP (addP l (scaleP 2 (mulXP (derivP l)))) (mulXP l)) x) x := by
  have h := ((hasDerivAt_id x).mul (hasDerivAt_evalP_sq l x)).mul (hasDerivAt_gauss x)
  have hf : phiO l = fun x => (id x * evalP l (2 * π * x ^ 2)) * gauss x := by
    funext y; simp [phiO]
  rw [hf]
  have e : phiE (subP (addP l (scaleP 2 (mulXP (derivP l)))) (mulXP l)) x =
      (1 * evalP l (2 * π * x ^ 2) + id x * (evalP (derivP l) (2 * π * x ^ 2) * (4 * π * x))) *
        gauss x + id x * evalP l (2 * π * x ^ 2) * (-2 * π * x * gauss x) := by
    simp only [phiE, evalP_subP, evalP_addP, evalP_scaleP, evalP_mulXP, id]; push_cast; ring
  rw [e]; exact h

/-! ## Fourier transform: the raising operator -/

theorem fourier_const_mul' (c : ℂ) (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => c * g x) ξ = c * 𝓕 g ξ := by
  simp only [fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext v; ring

theorem fourier_add' {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun x => f x + g x) ξ = 𝓕 f ξ + 𝓕 g ξ := by
  rw [fourier_eq, fourier_eq, fourier_eq]
  simp only [smul_add]
  exact integral_add ((fourierIntegral_convergent_iff ξ).2 hf)
    ((fourierIntegral_convergent_iff ξ).2 hg)

theorem fourier_sub' {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun x => f x - g x) ξ = 𝓕 f ξ - 𝓕 g ξ := by
  rw [fourier_eq, fourier_eq, fourier_eq]
  simp only [smul_sub]
  exact integral_sub ((fourierIntegral_convergent_iff ξ).2 hf)
    ((fourierIntegral_convergent_iff ξ).2 hg)

theorem fourier_raise {g g' : ℝ → ℂ} (hg : Integrable g)
    (hxg : Integrable (fun x : ℝ => (x : ℂ) * g x)) (hd : ∀ x, HasDerivAt g (g' x) x)
    (hg' : Integrable g') (ξ : ℝ) :
    𝓕 (fun x : ℝ => (2 * π * (x : ℂ)) * g x - g' x) ξ =
      -I * ((2 * π * (ξ : ℂ)) * 𝓕 g ξ - deriv (𝓕 g) ξ) := by
  have hxg' : Integrable (fun x : ℝ => x • g x) := by
    simpa [Complex.real_smul] using hxg
  have h1 : deriv (𝓕 g) ξ = (-2 * π * I) * 𝓕 (fun x : ℝ => (x : ℂ) * g x) ξ := by
    rw [deriv_fourier hg hxg']
    rw [← fourier_const_mul']
    have e : (fun x : ℝ => (-2 * π * I * x) • g x) = fun x : ℝ => (-2 * π * I) * ((x : ℂ) * g x) := by
      funext x; simp only [smul_eq_mul]; ring
    rw [e]
  have hdg : deriv g = g' := by funext x; exact (hd x).deriv
  have hdiff : Differentiable ℝ g := fun x => (hd x).differentiableAt
  have h2 : 𝓕 g' ξ = (2 * π * I * ξ) * 𝓕 g ξ := by
    have := congrFun (fourier_deriv hg hdiff (by rw [hdg]; exact hg')) ξ
    rw [hdg] at this
    rw [this]; simp
  have hA : Integrable (fun x : ℝ => (2 * π * (x : ℂ)) * g x) := by
    have := hxg.const_mul (2 * π : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  rw [fourier_sub' hA hg' ξ, h2, h1]
  have e : (fun x : ℝ => (2 * π * (x : ℂ)) * g x) = fun x : ℝ => (2 * π : ℂ) * ((x : ℂ) * g x) := by
    funext x; ring
  rw [e, fourier_const_mul']
  ring_nf
  rw [I_sq]; ring

theorem fourier_raise_eig {g g' : ℝ → ℂ} (hg : Integrable g)
    (hxg : Integrable (fun x : ℝ => (x : ℂ) * g x)) (hd : ∀ x, HasDerivAt g (g' x) x)
    (hg' : Integrable g') (c : ℂ) (hF : 𝓕 g = fun x => c * g x) :
    𝓕 (fun x : ℝ => (2 * π * (x : ℂ)) * g x - g' x) =
      fun ξ : ℝ => (-I * c) * ((2 * π * (ξ : ℂ)) * g ξ - g' ξ) := by
  funext ξ
  rw [fourier_raise hg hxg hd hg' ξ]
  have : deriv (𝓕 g) ξ = c * g' ξ := by rw [hF]; exact ((hd ξ).const_mul c).deriv
  rw [this, hF]; ring


/-! ## Fourier eigenfunctions of the form `q(2πx²) e^{-πx²}` -/

/-- Complexified even function. -/
noncomputable def cE (l : NP) (x : ℝ) : ℂ := (phiE l x : ℂ)

/-- Complexified odd function. -/
noncomputable def cO (l : NP) (x : ℝ) : ℂ := (phiO l x : ℂ)

/-- `a†` maps `q(t)G` to `4π · x (q - q')(t) G`. -/
def SevenP (l : NP) : NP := subP l (derivP l)

/-- `a†` maps `x r(t) G` to `((2t - 1) r - 2t r')(t) G`. -/
def SoddP (r : NP) : NP :=
  subP (subP (scaleP 2 (mulXP r)) r) (scaleP 2 (mulXP (derivP r)))

/-- Four raising steps, normalised: `(a†)^4 (q(t)G) = 16π² (TstepP q)(t) G`. -/
def TstepP (l : NP) : NP := SoddP (SevenP (SoddP (SevenP l)))

/-- `r₀ + T(r₁ + T(r₂ + ⋯))`: a combination of the eigenfunctions `Tstep^k 1`. -/
def hornerTP : List ℤ → NP
  | [] => ([], [])
  | r :: rs => addP ([r.toNat], [(-r).toNat]) (TstepP (hornerTP rs))

/-- `g` is an eigenfunction of the Fourier transform with eigenvalue `c`. -/
def IsEig (c : ℂ) (g : ℝ → ℂ) : Prop := 𝓕 g = fun x => c * g x

theorem integrable_cE (l : NP) : Integrable (cE l) := (integrable_phiE l).ofReal

theorem integrable_cO (l : NP) : Integrable (cO l) := (integrable_phiO l).ofReal

theorem integrable_x_cE (l : NP) : Integrable (fun x : ℝ => (x : ℂ) * cE l x) := by
  refine (integrable_x_mul_phiE l).ofReal.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [cE]

theorem integrable_x_cO (l : NP) : Integrable (fun x : ℝ => (x : ℂ) * cO l x) := by
  refine (integrable_x_mul_phiO l).ofReal.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [cO]

theorem eig_even_to_odd {c : ℂ} {l : NP} (h : IsEig c (cE l)) :
    IsEig (-I * c) (cO (SevenP l)) := by
  set g' : ℝ → ℂ := fun x => ((-2 * π * phiO (subP l (scaleP 2 (derivP l))) x : ℝ) : ℂ) with hg'
  have hd : ∀ x, HasDerivAt (cE l) (g' x) x := fun x => (hasDerivAt_phiE l x).ofReal_comp
  have hint : Integrable g' := ((integrable_phiO _).const_mul (-2 * π)).ofReal
  have key := fourier_raise_eig (integrable_cE l) (integrable_x_cE l) hd hint c h
  have hfun : (fun x : ℝ => (2 * π * (x : ℂ)) * cE l x - g' x) =
      fun x : ℝ => (4 * π : ℂ) * cO (SevenP l) x := by
    funext x
    simp only [hg', cE, cO, phiE, phiO, SevenP, evalP_subP, evalP_scaleP]
    push_cast; ring
  rw [hfun] at key
  unfold IsEig
  funext ξ
  have k2 := congrFun key ξ
  have k3 : (2 * π * (ξ : ℂ)) * cE l ξ - g' ξ = (4 * π : ℂ) * cO (SevenP l) ξ := congrFun hfun ξ
  rw [fourier_const_mul', k3] at k2
  have hne : (4 * π : ℂ) ≠ 0 := by
    have : (4 * π : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  apply mul_left_cancel₀ hne
  rw [k2]; ring

theorem eig_odd_to_even {c : ℂ} {r : NP} (h : IsEig c (cO r)) :
    IsEig (-I * c) (cE (SoddP r)) := by
  set g' : ℝ → ℂ := cE (subP (addP r (scaleP 2 (mulXP (derivP r)))) (mulXP r)) with hg'
  have hd : ∀ x, HasDerivAt (cO r) (g' x) x := fun x => (hasDerivAt_phiO r x).ofReal_comp
  have key := fourier_raise_eig (integrable_cO r) (integrable_x_cO r) hd (integrable_cE _) c h
  have hfun : (fun x : ℝ => (2 * π * (x : ℂ)) * cO r x - g' x) = cE (SoddP r) := by
    funext x
    simp only [hg', cE, cO, phiE, phiO, SoddP, evalP_subP, evalP_scaleP, evalP_addP, evalP_mulXP]
    push_cast; ring
  rw [hfun] at key
  unfold IsEig
  rw [key]
  funext ξ
  rw [← congrFun hfun ξ]

theorem eig_Tstep {c : ℂ} {l : NP} (h : IsEig c (cE l)) : IsEig c (cE (TstepP l)) := by
  have h4 := eig_odd_to_even (eig_even_to_odd (eig_odd_to_even (eig_even_to_odd h)))
  have e : -I * (-I * (-I * (-I * c))) = c := by
    have : -I * (-I * (-I * (-I * c))) = (I ^ 2) ^ 2 * c := by ring
    rw [this, I_sq]; ring
  rw [e] at h4
  exact h4

theorem eig_const (c : ℤ) : IsEig 1 (cE ([c.toNat], [(-c).toNat])) := by
  have hc : ((c.toNat : ℕ) : ℝ) - (((-c).toNat : ℕ) : ℝ) = (c : ℝ) := by
    have := Int.toNat_sub_toNat_neg c
    exact_mod_cast this
  have hf : cE ([c.toNat], [(-c).toNat]) = fun x : ℝ => (c : ℂ) * cexp (-π * (1 : ℂ) * x ^ 2) := by
    funext x
    simp only [cE, phiE, gauss, evalP, evalN_cons, evalN_nil, mul_zero, add_zero]
    rw [hc]
    push_cast; ring_nf
  unfold IsEig
  rw [hf]
  funext ξ
  rw [fourier_const_mul', fourier_gaussian_pi (by simp)]
  simp

theorem eig_nil : IsEig 1 (cE ([], [])) := by
  have hf : cE ([], []) = fun _ : ℝ => (0 : ℂ) := by
    funext x; simp [cE, phiE, evalP]
  unfold IsEig
  rw [hf]
  funext ξ
  simp [fourier_eq]

theorem eig_add {p q : NP} (hp : IsEig 1 (cE p)) (hq : IsEig 1 (cE q)) :
    IsEig 1 (cE (addP p q)) := by
  have hf : cE (addP p q) = fun x => cE p x + cE q x := by
    funext x; simp only [cE, phiE, evalP_addP]; push_cast; ring
  unfold IsEig at *
  rw [hf]
  funext ξ
  rw [fourier_add' (integrable_cE p) (integrable_cE q), hp, hq]
  ring

/-- Every `Q = r₀ + T(r₁ + T(r₂ + ⋯))` gives a Fourier-invariant `Q(2πx²) e^{-πx²}`. -/
theorem eig_hornerTP (rs : List ℤ) : IsEig 1 (cE (hornerTP rs)) := by
  induction rs with
  | nil => exact eig_nil
  | cons r rs ih => exact eig_add (eig_const r) (eig_Tstep ih)

/-! ## Exact positivity certificates (natural-number arithmetic) -/

/-- Coefficients of `(α + v) q(v) + prev` (helper for `compLinN`). -/
def mulLinN (α : ℕ) : ℕ → List ℕ → List ℕ
  | prev, [] => [prev]
  | prev, a :: q => (α * a + prev) :: mulLinN α a q

def addHeadN (c : ℕ) : List ℕ → List ℕ
  | [] => [c]
  | a :: q => (c + a) :: q

/-- Coefficients of `p(α + v)` (Taylor shift). -/
def compLinN (α : ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: cs => addHeadN c (mulLinN α 0 (compLinN α cs))

/-- Coefficient `j` multiplied by `M^(len - 1 - j)`, so that `p(u/M) M^(len-1)` results. -/
def scaleUpN (M : ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: cs => (c * M ^ cs.length) :: scaleUpN M cs

/-- Coefficientwise `wn ≤ wp` (equal lengths). -/
def leL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: p, b :: q => decide (b ≤ a) && leL p q
  | _, _ => false

/-- `wp - wn` has nonnegative coefficients and positive constant term. -/
def tailOKP : List ℕ → List ℕ → Bool
  | a :: p, b :: q => decide (b < a) && leL p q
  | _, _ => false

theorem evalN_mulLinN {R : Type*} [CommSemiring R] (α prev : ℕ) (q : List ℕ) (v : R) :
    evalN (mulLinN α prev q) v = ((α : R) + v) * evalN q v + prev := by
  induction q generalizing prev with
  | nil => simp [mulLinN]
  | cons a q ih => simp [mulLinN, ih]; ring

theorem evalN_addHeadN {R : Type*} [CommSemiring R] (c : ℕ) (q : List ℕ) (v : R) :
    evalN (addHeadN c q) v = c + evalN q v := by
  cases q <;> simp [addHeadN]; ring

theorem evalN_compLinN {R : Type*} [CommSemiring R] (α : ℕ) (p : List ℕ) (v : R) :
    evalN (compLinN α p) v = evalN p ((α : R) + v) := by
  induction p with
  | nil => simp [compLinN]
  | cons c cs ih => simp [compLinN, evalN_addHeadN, evalN_mulLinN, ih]

theorem evalN_scaleUpN (M : ℕ) (p : List ℕ) (t : ℝ) :
    (M : ℝ) * evalN (scaleUpN M p) ((M : ℝ) * t) = (M : ℝ) ^ p.length * evalN p t := by
  induction p with
  | nil => simp [scaleUpN]
  | cons c cs ih =>
    simp only [scaleUpN, evalN_cons, List.length_cons]
    push_cast
    have : (M : ℝ) * ((M : ℝ) * t * evalN (scaleUpN M cs) ((M : ℝ) * t)) =
        (M : ℝ) * t * ((M : ℝ) * evalN (scaleUpN M cs) ((M : ℝ) * t)) := by ring
    rw [mul_add, this, ih]; ring

theorem leL_nonneg {p q : List ℕ} (h : leL p q = true) (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ evalN p v - evalN q v := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => simp
    | cons b q => simp [leL] at h
  | cons a p ih =>
    cases q with
    | nil => simp [leL] at h
    | cons b q =>
      simp only [leL, Bool.and_eq_true, decide_eq_true_eq] at h
      have h1 : (b : ℝ) ≤ a := by exact_mod_cast h.1
      have h2 := ih h.2
      simp only [evalN_cons]
      nlinarith

theorem tailOKP_pos {p q : List ℕ} (h : tailOKP p q = true) (v : ℝ) (hv : 0 ≤ v) :
    0 < evalN p v - evalN q v := by
  match p, q, h with
  | a :: p, b :: q, h =>
    simp only [tailOKP, Bool.and_eq_true, decide_eq_true_eq] at h
    have h1 : (b : ℝ) < a := by exact_mod_cast h.1
    have h2 := leL_nonneg h.2 v hv
    simp only [evalN_cons]
    nlinarith

theorem tail_pos (Zp Zn : List ℕ) (A : ℕ) (h : tailOKP (compLinN A Zp) (compLinN A Zn) = true)
    (u : ℝ) (hu : (A : ℝ) ≤ u) : 0 < evalN Zp u - evalN Zn u := by
  have := tailOKP_pos h (u - A) (by linarith)
  rw [evalN_compLinN, evalN_compLinN] at this
  simpa using this

/-! ## Descartes-type leaf certificates -/

/-- Coefficient `i` multiplied by `pw · W^i`, so that `p(W y)·pw` results. -/
def mulPowAux (W : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | pw, c :: cs => (c * pw) :: mulPowAux W (pw * W) cs

theorem evalN_mulPowAux (W pw : ℕ) (p : List ℕ) (y : ℝ) :
    evalN (mulPowAux W pw p) y = pw * evalN p ((W : ℝ) * y) := by
  induction p generalizing pw with
  | nil => simp [mulPowAux]
  | cons c cs ih => simp only [mulPowAux, evalN_cons, ih]; push_cast; ring

theorem evalN_append_single (l : List ℕ) (c : ℕ) (z : ℝ) :
    evalN (l ++ [c]) z = evalN l z + c * z ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, evalN_cons, ih, List.length_cons]; ring

theorem evalN_reverse (l : List ℕ) {z : ℝ} (hz : z ≠ 0) :
    z * evalN l.reverse z = z ^ l.length * evalN l z⁻¹ := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    simp only [List.reverse_cons, evalN_append_single, List.length_reverse, evalN_cons,
      List.length_cons, mul_add, ih]
    field_simp
    ring

theorem evalN_zero (l : List ℕ) : evalN l (0 : ℝ) = (l.getD 0 0 : ℕ) := by
  cases l <;> simp

/-- Leaf test for `p = P - N` on `[0, 1]`: `p(0) > 0` and all coefficients of
`(1+z)^deg p(1/(1+z))` are `≥ 0` with positive constant term. -/
def leafOK (pp pn : List ℕ) : Bool :=
  decide (pn.getD 0 0 < pp.getD 0 0) && tailOKP (compLinN 1 pp.reverse) (compLinN 1 pn.reverse)

theorem leafOK_pos {pp pn : List ℕ} (hlen : pp.length = pn.length) (h : leafOK pp pn = true)
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 < evalN pp y - evalN pn y := by
  unfold leafOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases eq_or_lt_of_le hy0 with hy | hy
  · subst hy
    rw [evalN_zero, evalN_zero]
    have : ((pn.getD 0 0 : ℕ) : ℝ) < ((pp.getD 0 0 : ℕ) : ℝ) := by exact_mod_cast h.1
    linarith
  · set w : ℝ := y⁻¹ with hw
    have hwpos : 0 < w := inv_pos.mpr hy
    have hz : 0 ≤ w - 1 := by
      have : 1 ≤ w := by rw [hw]; exact one_le_inv₀ hy |>.mpr hy1
      linarith
    have hq := tailOKP_pos h.2 (w - 1) hz
    rw [evalN_compLinN, evalN_compLinN] at hq
    push_cast at hq
    have e : (1 : ℝ) + (w - 1) = w := by ring
    rw [e] at hq
    have r1 := evalN_reverse pp hwpos.ne'
    have r2 := evalN_reverse pn hwpos.ne'
    rw [hw, inv_inv] at r1 r2
    rw [hlen] at r1
    have key : y⁻¹ * (evalN pp.reverse y⁻¹ - evalN pn.reverse y⁻¹) =
        y⁻¹ ^ pn.length * (evalN pp y - evalN pn y) := by
      rw [mul_sub, r1, r2]; ring
    have : 0 < y⁻¹ ^ pn.length * (evalN pp y - evalN pn y) := by
      rw [← key]; exact mul_pos (inv_pos.mpr hy) hq
    exact pos_of_mul_pos_right this (by positivity)

/-- A chain of leaves `[A, A + W]` covering `[lo, hi]` for `Zp - Zn`. -/
def leavesOK (Zp Zn : List ℕ) : ℕ → List (ℕ × ℕ) → ℕ → Bool
  | lo, [], hi => decide (hi ≤ lo)
  | lo, (A, W) :: ls, hi =>
      decide (A ≤ lo) && decide (0 < W) &&
        leafOK (mulPowAux W 1 (compLinN A Zp)) (mulPowAux W 1 (compLinN A Zn)) &&
        leavesOK Zp Zn (A + W) ls hi

theorem length_compLinN (A : ℕ) (p : List ℕ) : (compLinN A p).length = p.length := by
  induction p with
  | nil => simp [compLinN]
  | cons c cs ih =>
    simp only [compLinN, List.length_cons]
    have h1 : ∀ (prev : ℕ) (q : List ℕ), (mulLinN A prev q).length = q.length + 1 := by
      intro prev q
      induction q generalizing prev with
      | nil => simp [mulLinN]
      | cons a q ihq => simp [mulLinN, ihq]
    have h2 : ∀ (c : ℕ) (q : List ℕ), q ≠ [] → (addHeadN c q).length = q.length := by
      intro c q hq
      cases q with
      | nil => exact absurd rfl hq
      | cons a q => simp [addHeadN]
    rw [h2 _ _ (by rw [← List.length_pos_iff]; rw [h1]; omega), h1, ih]

theorem length_mulPowAux (W pw : ℕ) (p : List ℕ) : (mulPowAux W pw p).length = p.length := by
  induction p generalizing pw with
  | nil => simp [mulPowAux]
  | cons c cs ih => simp [mulPowAux, ih]

theorem leavesOK_leaf {Zp Zn : List ℕ} (hlen : Zp.length = Zn.length) {A W : ℕ} (hW : 0 < W)
    (h : leafOK (mulPowAux W 1 (compLinN A Zp)) (mulPowAux W 1 (compLinN A Zn)) = true)
    (u : ℝ) (h1 : (A : ℝ) ≤ u) (h2 : u ≤ ((A + W : ℕ) : ℝ)) : 0 < evalN Zp u - evalN Zn u := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hl : (mulPowAux W 1 (compLinN A Zp)).length = (mulPowAux W 1 (compLinN A Zn)).length := by
    simp [length_mulPowAux, length_compLinN, hlen]
  have hq := leafOK_pos hl h ((u - A) / W) (div_nonneg (by linarith) hWr.le)
    (by rw [div_le_one hWr]; push_cast at h2; linarith)
  rw [evalN_mulPowAux, evalN_mulPowAux, evalN_compLinN, evalN_compLinN] at hq
  have e : (A : ℝ) + (W : ℝ) * ((u - A) / W) = u := by field_simp; ring
  simpa [e] using hq

theorem leavesOK_pos_aux (Zp Zn : List ℕ) (hlen : Zp.length = Zn.length) (lo : ℕ)
    (ls : List (ℕ × ℕ)) (hi : ℕ) (h : leavesOK Zp Zn lo ls hi = true) (u : ℝ)
    (hlo : (lo : ℝ) < u) (hhi : u ≤ hi) : 0 < evalN Zp u - evalN Zn u := by
  induction ls generalizing lo with
  | nil =>
    simp only [leavesOK, decide_eq_true_eq] at h
    have : (hi : ℝ) ≤ lo := by exact_mod_cast h
    linarith
  | cons e ls ih =>
    obtain ⟨A, W⟩ := e
    simp only [leavesOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    by_cases hu : u ≤ ((A + W : ℕ) : ℝ)
    · have hA : (A : ℝ) ≤ lo := by exact_mod_cast h1
      exact leavesOK_leaf hlen h2 h3 u (by linarith) hu
    · exact ih (A + W) h4 (not_le.mp hu)

theorem leavesOK_pos (Zp Zn : List ℕ) (hlen : Zp.length = Zn.length) (lo : ℕ)
    (ls : List (ℕ × ℕ)) (hne : ls ≠ []) (hi : ℕ) (h : leavesOK Zp Zn lo ls hi = true) (u : ℝ)
    (hlo : (lo : ℝ) ≤ u) (hhi : u ≤ hi) : 0 < evalN Zp u - evalN Zn u := by
  cases ls with
  | nil => exact absurd rfl hne
  | cons e ls =>
    obtain ⟨A, W⟩ := e
    have h' := h
    simp only [leavesOK, Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
    by_cases hu : u ≤ ((A + W : ℕ) : ℝ)
    · have hA : (A : ℝ) ≤ lo := by exact_mod_cast h1
      exact leavesOK_leaf hlen h2 h3 u (by linarith) hu
    · exact leavesOK_pos_aux Zp Zn hlen (A + W) ls hi h4 u (not_le.mp hu) hhi

/-! ## The sign uncertainty constant -/

/-- `A(g) = inf {r > 0 : g(x) ≥ 0 for all |x| ≥ r}` (the last sign change radius). -/
noncomputable def lastSignChange (g : ℝ → ℝ) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ ∀ x : ℝ, r ≤ |x| → 0 ≤ g x}

/-- Real part of `f̂(ξ) = ∫ f(x) e^{-2πixξ} dx` (Mathlib's normalisation of `𝓕`). -/
noncomputable def fourierRe (f : ℝ → ℝ) (ξ : ℝ) : ℝ := (𝓕 (fun x => (f x : ℂ)) ξ).re

/-- The admissible class: continuous, even, integrable `f` with integrable real `f̂`,
`f(0) < 0`, `f̂(0) < 0`, and both `f`, `f̂` eventually nonnegative (otherwise `A = ∞`, which
does not affect the infimum). The extra regularity only shrinks the class, so the infimum
below is at least the constant over any larger class containing these functions. -/
structure Admissible (f : ℝ → ℝ) : Prop where
  continuous : Continuous f
  integrable : Integrable f
  even : ∀ x, f (-x) = f x
  fourier_integrable : Integrable (𝓕 (fun x => (f x : ℂ)))
  fourier_real : ∀ ξ, (𝓕 (fun x => (f x : ℂ)) ξ).im = 0
  zero_neg : f 0 < 0
  fourier_zero_neg : fourierRe f 0 < 0
  eventually_nonneg : ∃ r, 0 < r ∧ ∀ x, r ≤ |x| → 0 ≤ f x
  fourier_eventually_nonneg : ∃ r, 0 < r ∧ ∀ x, r ≤ |x| → 0 ≤ fourierRe f x

/-- The `+1` sign uncertainty constant `inf A(f) A(f̂)` over the admissible class. -/
noncomputable def signUncertaintyConstant : ℝ :=
  sInf {c : ℝ | ∃ f, Admissible f ∧ c = lastSignChange f * lastSignChange (fourierRe f)}

theorem lastSignChange_nonneg (g : ℝ → ℝ) : 0 ≤ lastSignChange g :=
  Real.sInf_nonneg (fun _ hr => le_of_lt hr.1)

theorem lastSignChange_le {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (h : ∀ x, r ≤ |x| → 0 ≤ g x) :
    lastSignChange g ≤ r :=
  csInf_le ⟨0, fun _ hs => le_of_lt hs.1⟩ ⟨hr, h⟩

theorem signUncertaintyConstant_le {f : ℝ → ℝ} (hf : Admissible f) {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (h₁' : ∀ x, r₁ ≤ |x| → 0 ≤ f x) (h₂ : 0 < r₂) (h₂' : ∀ x, r₂ ≤ |x| → 0 ≤ fourierRe f x) :
    signUncertaintyConstant ≤ r₁ * r₂ := by
  have hmem : lastSignChange f * lastSignChange (fourierRe f) ∈
      {c : ℝ | ∃ f, Admissible f ∧ c = lastSignChange f * lastSignChange (fourierRe f)} :=
    ⟨f, hf, rfl⟩
  have hbdd : BddBelow
      {c : ℝ | ∃ f, Admissible f ∧ c = lastSignChange f * lastSignChange (fourierRe f)} := by
    refine ⟨0, fun c hc => ?_⟩
    obtain ⟨g, _, rfl⟩ := hc
    exact mul_nonneg (lastSignChange_nonneg _) (lastSignChange_nonneg _)
  calc signUncertaintyConstant ≤ lastSignChange f * lastSignChange (fourierRe f) :=
        csInf_le hbdd hmem
    _ ≤ r₁ * r₂ := mul_le_mul (lastSignChange_le h₁ h₁') (lastSignChange_le h₂ h₂')
        (lastSignChange_nonneg _) h₁.le

/-- Scaled positivity on `[lo, hi]` transfers to `evalP` on `[lo/M, hi/M]`. -/
theorem evalP_pos_of_scaled {Zp Zn : List ℕ} (hlen : Zp.length = Zn.length) {M : ℕ} (hM : 0 < M)
    {t : ℝ} (h : 0 < evalN (scaleUpN M Zp) ((M : ℝ) * t) - evalN (scaleUpN M Zn) ((M : ℝ) * t)) :
    0 < evalP ((Zp, Zn) : NP) t := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hs1 := evalN_scaleUpN M Zp t
  have hs2 := evalN_scaleUpN M Zn t
  rw [hlen] at hs1
  have hdiff : (M : ℝ) * (evalN (scaleUpN M Zp) ((M : ℝ) * t) - evalN (scaleUpN M Zn) ((M : ℝ) * t)) =
      (M : ℝ) ^ Zn.length * evalP ((Zp, Zn) : NP) t := by
    rw [mul_sub, hs1, hs2]; simp only [evalP]; ring
  have : 0 < (M : ℝ) ^ Zn.length * evalP ((Zp, Zn) : NP) t := by rw [← hdiff]; positivity
  exact pos_of_mul_pos_right this (by positivity)

theorem length_scaleUpN (M : ℕ) (p : List ℕ) : (scaleUpN M p).length = p.length := by
  induction p with
  | nil => simp [scaleUpN]
  | cons c cs ih => simp [scaleUpN, ih]

/-- A chain of Descartes leaves certifies `[lo/M, hi/M]`. -/
theorem chunk_leaves {Zp Zn : List ℕ} (hlen : Zp.length = Zn.length) {M lo hi : ℕ} (hM : 0 < M)
    {ls : List (ℕ × ℕ)} (hne : ls ≠ []) (h : leavesOK (scaleUpN M Zp) (scaleUpN M Zn) lo ls hi = true) :
    ∀ t : ℝ, (lo : ℝ) / M ≤ t → t ≤ (hi : ℝ) / M → 0 < evalP ((Zp, Zn) : NP) t := by
  intro t h1 h2
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  apply evalP_pos_of_scaled hlen hM
  apply leavesOK_pos _ _ (by simp [length_scaleUpN, hlen]) lo ls hne hi h
  · rw [div_le_iff₀ hMr] at h1; linarith
  · rw [le_div_iff₀ hMr] at h2; linarith

/-- The certified tail `[A/M, ∞)`. -/
theorem chunk_tail {Zp Zn : List ℕ} (hlen : Zp.length = Zn.length) {M A : ℕ} (hM : 0 < M)
    (h : tailOKP (compLinN A (scaleUpN M Zp)) (compLinN A (scaleUpN M Zn)) = true) :
    ∀ t : ℝ, (A : ℝ) / M ≤ t → 0 < evalP ((Zp, Zn) : NP) t := by
  intro t h1
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  apply evalP_pos_of_scaled hlen hM
  apply tail_pos _ _ A h
  rw [div_le_iff₀ hMr] at h1; linarith

/-- Glue a certified range `[a, b]` to a certified ray `[b', ∞)` with `b' ≤ b`. -/
theorem pos_glue {P : ℝ → Prop} {a b b' : ℝ} (h₁ : ∀ t : ℝ, a ≤ t → t ≤ b → P t)
    (h₂ : ∀ t : ℝ, b' ≤ t → P t) (hb : b' ≤ b) : ∀ t : ℝ, a ≤ t → P t := by
  intro t ht
  by_cases h : t ≤ b
  · exact h₁ t ht h
  · exact h₂ t (hb.trans (le_of_lt (not_le.mp h)))

/-- An integer combination `Q = hornerTP rs = (Zp, Zn)` with `Q(0) < 0` and `Q > 0` on
`[R, ∞)` gives `signUncertaintyConstant ≤ R / (2π)`. -/
theorem bound_of_certificate (rs : List ℤ) (Zp Zn : List ℕ) (R : ℝ)
    (hP : hornerTP rs = (Zp, Zn)) (hR : 0 < R) (h0 : Zp.getD 0 0 < Zn.getD 0 0)
    (hpos : ∀ t : ℝ, R ≤ t → 0 < evalP ((Zp, Zn) : NP) t) :
    signUncertaintyConstant ≤ R / (2 * π) := by
  set l : NP := (Zp, Zn) with hl
  set f : ℝ → ℝ := phiE l with hf
  have heig : IsEig 1 (cE l) := by
    have := eig_hornerTP rs
    rwa [hP] at this
  have hFf : 𝓕 (fun x => (f x : ℂ)) = fun x => (f x : ℂ) := by
    have : (fun x => (f x : ℂ)) = cE l := rfl
    rw [this, heig]; funext x; simp
  have hfre : fourierRe f = f := by
    funext ξ; simp [fourierRe, hFf]
  set r : ℝ := Real.sqrt (R / (2 * π)) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r * r = R / (2 * π) := Real.mul_self_sqrt (by positivity)
  have hnonneg : ∀ x, r ≤ |x| → 0 ≤ f x := by
    intro x hx
    have hx2 : R / (2 * π) ≤ x ^ 2 := by
      rw [← hr2, ← sq_abs x]; nlinarith [hrpos.le]
    have ht : R ≤ 2 * π * x ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hx2; linarith
    have hev := hpos _ ht
    simp only [hf, phiE]
    exact mul_nonneg hev.le (Real.exp_pos _).le
  have hf0 : f 0 < 0 := by
    simp only [hf, phiE, gauss, evalP, hl]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Real.exp_zero, mul_one]
    rw [evalN_zero, evalN_zero]
    have : ((Zp.getD 0 0 : ℕ) : ℝ) < ((Zn.getD 0 0 : ℕ) : ℝ) := by exact_mod_cast h0
    linarith
  have hadm : Admissible f := by
    refine ⟨?_, integrable_phiE l, ?_, ?_, ?_, hf0, ?_, ⟨r, hrpos, hnonneg⟩, ?_⟩
    · exact continuous_iff_continuousAt.2 fun x => (hasDerivAt_phiE l x).continuousAt
    · intro x; simp [hf, phiE, gauss]
    · rw [hFf]; exact (integrable_phiE l).ofReal
    · intro ξ; rw [hFf]; simp
    · rw [hfre]; exact hf0
    · exact ⟨r, hrpos, by rw [hfre]; exact hnonneg⟩
  have := signUncertaintyConstant_le hadm hrpos hnonneg hrpos (by rw [hfre]; exact hnonneg)
  rwa [hr2] at this

end FleetSignUncertainty
