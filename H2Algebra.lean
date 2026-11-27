import Sobolev1D
import L2Embedding
import Mathlib

/-!
# Algebraic structure on `H2 L` and compatibility with the L² embedding

`H2 L` (from `Sobolev1D`) is a plain structure: a function `f : ℝ → ℝ` together
with regularity data on `[0,L]`.  This file equips it with the vector-space
operations a Friedrichs-extension domain needs and shows that the L² embedding
`L2Embedding.toL2` respects them.

## What is proven (standard axioms only)

* `H2.ofInterior` — a constructor building an `H2 L` element from a function `g`
  and a candidate derivative `g'` that are well behaved on `[0,L]` only.  The
  function is extended *linearly* outside `[0,L]` with slopes `g' 0`, `g' L`,
  so that the junk value of `deriv` at the endpoints is under control:
  `H2.ofInterior_deriv_eq` gives `deriv f x = g' x` for **all** `x ∈ Icc 0 L`.
* `H2.add hL u v`, `H2.smul c u`, `H2.zero` with `Add`, `SMul ℝ`, `Zero`
  instances (`Add` needs `[Fact (0 < L)]`, see below).
* `H2.add_f_eq` / `H2.add_deriv_eq` — on `Icc 0 L` the sum is `u.f + v.f` and
  its derivative is `deriv u.f + deriv v.f`.
* `H2Algebra.toL2_add`, `toL2_smul`, `toL2_zero` — `toL2` is additive,
  homogeneous, and sends `zero` to `0`.
* `H2Algebra.inner_toL2_add_left`, `inner_toL2_smul_left`, `integral_add_mul` —
  the induced bilinearity of the L² pairing.

## Why `add` needs `0 < L`

With `f := u.f + v.f` verbatim, the field `hdf_cont : ContinuousOn (deriv f)
(Icc 0 L)` can FAIL: `deriv` is a junk `0` where `f` is not differentiable,
and `u.f + v.f` can be non-differentiable at an endpoint even when `u.f`,
`v.f` are (e.g. a kink to the left of `0`).  The linear extension repairs this
but requires `Icc 0 L` to be a right-neighbourhood of `0`, i.e. `0 < L`.
(For `L ≤ 0` the sum is genuinely ill-defined: `deriv (u.f + v.f)` need not be
integrable on `[L,0]`.)  `smul` and `zero` need no such hypothesis.

## What is NOT proven

No `AddCommGroup (H2 L)` instance (the operations are not literally
associative as functions on `ℝ` because of the extension outside `[0,L]`; only
equality on `Icc 0 L` holds), no closedness/density, no Friedrichs extension.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace H2

variable {L : ℝ}

/-! ### Linear extension outside `[0,L]` -/

/-- `glue L a b g` agrees with `g` on `[0,L]`, is the line of slope `a`
through the origin on `(-∞,0]`, and the line of slope `b` through `(L,0)` on
`[L,∞)`. -/
def glue (L a b : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < 0 then a * x else if x ≤ L then g x else b * (x - L)

/-- `glue` agrees with `g` on `Icc 0 L`. -/
theorem glue_eq_of_mem_Icc {a b : ℝ} {g : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc 0 L) :
    glue L a b g x = g x := by
  unfold glue
  rw [if_neg (not_lt.mpr hx.1), if_pos hx.2]

/-- `glue` is the line `a * x` on `Iic 0` (using `g 0 = 0`). -/
theorem glue_eq_of_mem_Iic {a b : ℝ} {g : ℝ → ℝ} (hg0 : g 0 = 0) (hL : 0 < L) {x : ℝ}
    (hx : x ∈ Iic 0) : glue L a b g x = a * x := by
  unfold glue
  rcases lt_or_eq_of_le (mem_Iic.mp hx) with h | h
  · rw [if_pos h]
  · subst h
    rw [if_neg (lt_irrefl 0), if_pos hL.le, hg0, mul_zero]

/-- `glue` is the line `b * (x - L)` on `Ici L` (using `g L = 0`). -/
theorem glue_eq_of_mem_Ici {a b : ℝ} {g : ℝ → ℝ} (hgL : g L = 0) (hL : 0 < L) {x : ℝ}
    (hx : x ∈ Ici L) : glue L a b g x = b * (x - L) := by
  unfold glue
  have hx0 : ¬ x < 0 := not_lt.mpr (hL.le.trans (mem_Ici.mp hx))
  rw [if_neg hx0]
  rcases lt_or_eq_of_le (mem_Ici.mp hx) with h | h
  · rw [if_neg (not_le.mpr h)]
  · subst h
    rw [if_pos le_rfl, hgL, sub_self, mul_zero]

/-! ### Interval integrability from equality on the open interval -/

/-- If `f` is interval-integrable on `[0,L]` and `g = f` on the OPEN interval
`(0,L)`, then `g` is interval-integrable too (endpoints have measure zero). -/
theorem intervalIntegrable_of_eqOn_Ioo (hL : 0 < L) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 L) (h : ∀ x ∈ Ioo 0 L, f x = g x) :
    IntervalIntegrable g volume 0 L := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le] at hf ⊢
  refine hf.congr_fun_ae ?_
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ h)

/-! ### The constructor -/

/-- Build an `H2 L` element from data that is only controlled on `[0,L]`:
`g` continuous on `Icc 0 L` with `g 0 = g L = 0`, a function `g'` with
`HasDerivAt g (g' x) x` on `Ioo 0 L`, `g'` continuous on `Icc 0 L` and
differentiable on `Ioo 0 L`, and `deriv g'` interval-integrable.
The underlying function is `glue L (g' 0) (g' L) g`. -/
def ofInterior (hL : 0 < L) (g g' : ℝ → ℝ)
    (hg_cont : ContinuousOn g (Icc 0 L)) (hg0 : g 0 = 0) (hgL : g L = 0)
    (hg' : ∀ x ∈ Ioo 0 L, HasDerivAt g (g' x) x)
    (hg'_cont : ContinuousOn g' (Icc 0 L))
    (hg'_diff : DifferentiableOn ℝ g' (Ioo 0 L))
    (hg'' : IntervalIntegrable (deriv g') volume 0 L) : H2 L :=
  -- interior derivative of the glued function
  have hglue_Ioo : ∀ x ∈ Ioo 0 L, deriv (glue L (g' 0) (g' L) g) x = g' x := by
    intro x hx
    have hev : glue L (g' 0) (g' L) g =ᶠ[𝓝 x] g :=
      eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx)
        (fun y hy => glue_eq_of_mem_Icc (Ioo_subset_Icc_self hy))
    rw [hev.deriv_eq]
    exact (hg' x hx).deriv
  have hg_diff : DifferentiableOn ℝ g (Ioo 0 L) :=
    fun x hx => (hg' x hx).differentiableAt.differentiableWithinAt
  have hderiv_g : ∀ x ∈ Ioo 0 L, deriv g x = g' x := fun x hx => (hg' x hx).deriv
  -- derivative at the left endpoint
  have h0 : HasDerivAt (glue L (g' 0) (g' L) g) (g' 0) 0 := by
    have hleft : HasDerivWithinAt (glue L (g' 0) (g' L) g) (g' 0) (Iic 0) 0 := by
      have hlin : HasDerivAt (fun x : ℝ => g' 0 * x) (g' 0) 0 := by
        simpa using (hasDerivAt_id (0:ℝ)).const_mul (g' 0)
      exact hlin.hasDerivWithinAt.congr
        (fun y hy => glue_eq_of_mem_Iic hg0 hL hy)
        (glue_eq_of_mem_Iic hg0 hL (mem_Iic.mpr le_rfl))
    have hright : HasDerivWithinAt (glue L (g' 0) (g' L) g) (g' 0) (Ici 0) 0 := by
      have hg_right : HasDerivWithinAt g (g' 0) (Ici 0) 0 := by
        refine hasDerivWithinAt_Ici_of_tendsto_deriv hg_diff
          ((hg_cont 0 (left_mem_Icc.mpr hL.le)).mono Ioo_subset_Icc_self)
          (Ioo_mem_nhdsGT hL) ?_
        have ht : Tendsto g' (𝓝[>] 0) (𝓝 (g' 0)) :=
          (hg'_cont 0 (left_mem_Icc.mpr hL.le)).tendsto.mono_left
            (nhdsWithin_le_of_mem (Icc_mem_nhdsGT hL))
        refine ht.congr' ?_
        exact eventuallyEq_of_mem (Ioo_mem_nhdsGT hL) (fun y hy => (hderiv_g y hy).symm)
      refine hg_right.congr_of_eventuallyEq ?_ (glue_eq_of_mem_Icc (left_mem_Icc.mpr hL.le))
      exact eventuallyEq_of_mem (Icc_mem_nhdsGE hL) (fun y hy => glue_eq_of_mem_Icc hy)
    have := hleft.union hright
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  -- derivative at the right endpoint
  have hLd : HasDerivAt (glue L (g' 0) (g' L) g) (g' L) L := by
    have hright : HasDerivWithinAt (glue L (g' 0) (g' L) g) (g' L) (Ici L) L := by
      have hlin : HasDerivAt (fun x : ℝ => g' L * (x - L)) (g' L) L := by
        simpa using ((hasDerivAt_id L).sub_const L).const_mul (g' L)
      exact hlin.hasDerivWithinAt.congr
        (fun y hy => glue_eq_of_mem_Ici hgL hL hy)
        (glue_eq_of_mem_Ici hgL hL (mem_Ici.mpr le_rfl))
    have hleft : HasDerivWithinAt (glue L (g' 0) (g' L) g) (g' L) (Iic L) L := by
      have hg_left : HasDerivWithinAt g (g' L) (Iic L) L := by
        refine hasDerivWithinAt_Iic_of_tendsto_deriv hg_diff
          (hg_cont L (right_mem_Icc.mpr hL.le) |>.mono Ioo_subset_Icc_self)
          (Ioo_mem_nhdsLT hL) ?_
        have ht : Tendsto g' (𝓝[<] L) (𝓝 (g' L)) :=
          (hg'_cont L (right_mem_Icc.mpr hL.le)).tendsto.mono_left
            (nhdsWithin_le_of_mem (Icc_mem_nhdsLT hL))
        refine ht.congr' ?_
        exact eventuallyEq_of_mem (Ioo_mem_nhdsLT hL) (fun y hy => (hderiv_g y hy).symm)
      refine hg_left.congr_of_eventuallyEq ?_ (glue_eq_of_mem_Icc (right_mem_Icc.mpr hL.le))
      exact eventuallyEq_of_mem (Icc_mem_nhdsLE hL) (fun y hy => glue_eq_of_mem_Icc hy)
    have := hleft.union hright
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  -- derivative on the closed interval
  have hglue_Icc : ∀ x ∈ Icc 0 L, deriv (glue L (g' 0) (g' L) g) x = g' x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; exact h0.deriv
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · rw [h']; exact hLd.deriv
    exact hglue_Ioo x ⟨h, h'⟩
  have hdcont : ContinuousOn (deriv (glue L (g' 0) (g' L) g)) (Icc 0 L) :=
    hg'_cont.congr (fun x hx => hglue_Icc x hx)
  { f := glue L (g' 0) (g' L) g
    hf_diff := hg_diff.congr (fun x hx => glue_eq_of_mem_Icc (Ioo_subset_Icc_self hx))
    hf_cont := hg_cont.congr (fun x hx => glue_eq_of_mem_Icc hx)
    bc_left := by rw [glue_eq_of_mem_Icc (left_mem_Icc.mpr hL.le), hg0]
    bc_right := by rw [glue_eq_of_mem_Icc (right_mem_Icc.mpr hL.le), hgL]
    hdf_int := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hL.le]; exact hdcont
    hdf_diff := hg'_diff.congr (fun x hx => hglue_Icc x (Ioo_subset_Icc_self hx))
    hdf_cont := hdcont
    hddf_int := by
      refine intervalIntegrable_of_eqOn_Ioo hL hg'' (fun x hx => ?_)
      have hev : deriv (glue L (g' 0) (g' L) g) =ᶠ[𝓝 x] g' :=
        eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx) (fun y hy => hglue_Ioo y hy)
      exact hev.deriv_eq.symm }

/-- On `Icc 0 L`, the function of `ofInterior` is `g`. -/
theorem ofInterior_f_eq (hL : 0 < L) (g g' : ℝ → ℝ) hg_cont hg0 hgL hg' hg'_cont hg'_diff hg''
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    (ofInterior hL g g' hg_cont hg0 hgL hg' hg'_cont hg'_diff hg'').f x = g x :=
  glue_eq_of_mem_Icc hx

/-- On all of `Icc 0 L` (endpoints included), the derivative of the function
of `ofInterior` is `g'`.  This is the point of the linear extension. -/
theorem ofInterior_deriv_eq (hL : 0 < L) (g g' : ℝ → ℝ) hg_cont hg0 hgL hg' hg'_cont hg'_diff
    hg'' {x : ℝ} (hx : x ∈ Icc 0 L) :
    deriv (ofInterior hL g g' hg_cont hg0 hgL hg' hg'_cont hg'_diff hg'').f x = g' x := by
  -- `deriv f` and `g'` are both continuous on `Icc 0 L` (the former by the
  -- `hdf_cont` field) and agree on the interior, hence at the endpoints too.
  -- interior points
  have hIoo : ∀ y ∈ Ioo 0 L,
      deriv (ofInterior hL g g' hg_cont hg0 hgL hg' hg'_cont hg'_diff hg'').f y = g' y := by
    intro y hy
    have hev : (ofInterior hL g g' hg_cont hg0 hgL hg' hg'_cont hg'_diff hg'').f =ᶠ[𝓝 y] g :=
      eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hy)
        (fun z hz => glue_eq_of_mem_Icc (Ioo_subset_Icc_self hz))
    rw [hev.deriv_eq]
    exact (hg' y hy).deriv
  -- endpoints: both sides are continuous on `Icc 0 L` and agree on the dense
  -- interior, so they agree at the endpoints.
  have hc1 : ContinuousOn
      (deriv (ofInterior hL g g' hg_cont hg0 hgL hg' hg'_cont hg'_diff hg'').f) (Icc 0 L) :=
    (ofInterior hL g g' hg_cont hg0 hgL hg' hg'_cont hg'_diff hg'').hdf_cont
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h
    have t1 := (hc1 0 (left_mem_Icc.mpr hL.le)).tendsto.mono_left
      (nhdsWithin_le_of_mem (Icc_mem_nhdsGT hL))
    have t2 := (hg'_cont 0 (left_mem_Icc.mpr hL.le)).tendsto.mono_left
      (nhdsWithin_le_of_mem (Icc_mem_nhdsGT hL))
    have t1' := t1.congr' (eventuallyEq_of_mem (Ioo_mem_nhdsGT hL) (fun y hy => hIoo y hy))
    exact tendsto_nhds_unique t1' t2
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · rw [h']
    have t1 := (hc1 L (right_mem_Icc.mpr hL.le)).tendsto.mono_left
      (nhdsWithin_le_of_mem (Icc_mem_nhdsLT hL))
    have t2 := (hg'_cont L (right_mem_Icc.mpr hL.le)).tendsto.mono_left
      (nhdsWithin_le_of_mem (Icc_mem_nhdsLT hL))
    have t1' := t1.congr' (eventuallyEq_of_mem (Ioo_mem_nhdsLT hL) (fun y hy => hIoo y hy))
    exact tendsto_nhds_unique t1' t2
  exact hIoo x ⟨h, h'⟩

/-! ### Addition -/

/-- The sum of two `H2 L` elements: `u.f + v.f` on `[0,L]`, extended linearly
outside.  Needs `0 < L` (see the module docstring). -/
def add (hL : 0 < L) (u v : H2 L) : H2 L :=
  ofInterior hL (u.f + v.f) (deriv u.f + deriv v.f)
    (u.hf_cont.add v.hf_cont)
    (by simp [u.bc_left, v.bc_left])
    (by simp [u.bc_right, v.bc_right])
    (fun x hx =>
      ((u.hf_diff.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt).add
        ((v.hf_diff.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt))
    (u.hdf_cont.add v.hdf_cont)
    (u.hdf_diff.add v.hdf_diff)
    (by
      refine intervalIntegrable_of_eqOn_Ioo hL (u.hddf_int.add v.hddf_int) (fun x hx => ?_)
      have := deriv_add (u.hdf_diff.differentiableAt (isOpen_Ioo.mem_nhds hx))
        (v.hdf_diff.differentiableAt (isOpen_Ioo.mem_nhds hx))
      simp only [Pi.add_def] at this ⊢
      exact this.symm)

/-- On `Icc 0 L`, `(add hL u v).f = u.f + v.f`. -/
theorem add_f_eq (hL : 0 < L) (u v : H2 L) {x : ℝ} (hx : x ∈ Icc 0 L) :
    (add hL u v).f x = u.f x + v.f x :=
  glue_eq_of_mem_Icc hx

/-- On `Icc 0 L` (endpoints included), `deriv (add hL u v).f = deriv u.f + deriv v.f`. -/
theorem add_deriv_eq (hL : 0 < L) (u v : H2 L) {x : ℝ} (hx : x ∈ Icc 0 L) :
    deriv (add hL u v).f x = deriv u.f x + deriv v.f x :=
  ofInterior_deriv_eq hL _ _ _ _ _ _ _ _ _ hx

/-! ### Scalar multiplication and zero -/

/-- Scalar multiple `c • u`, with function `fun x => c * u.f x`.  Here
`deriv (c * ·) = c * deriv ·` holds everywhere (`deriv_const_mul_field'`), so
no extension and no hypothesis on `L` is needed. -/
def smul (c : ℝ) (u : H2 L) : H2 L where
  f := fun x => c * u.f x
  hf_diff := u.hf_diff.const_mul c
  hf_cont := continuousOn_const.mul u.hf_cont
  bc_left := by simp [u.bc_left]
  bc_right := by simp [u.bc_right]
  hdf_int := by rw [deriv_const_mul_field']; exact u.hdf_int.const_mul c
  hdf_diff := by rw [deriv_const_mul_field']; exact u.hdf_diff.const_mul c
  hdf_cont := by rw [deriv_const_mul_field']; exact continuousOn_const.mul u.hdf_cont
  hddf_int := by
    rw [deriv_const_mul_field', deriv_const_mul_field']
    exact u.hddf_int.const_mul c

/-- `(smul c u).f x = c * u.f x` (definitional). -/
theorem smul_f_eq (c : ℝ) (u : H2 L) (x : ℝ) : (smul c u).f x = c * u.f x := rfl

/-- The zero element of `H2 L`. -/
def zero : H2 L where
  f := fun _ => 0
  hf_diff := differentiableOn_const 0
  hf_cont := continuousOn_const
  bc_left := rfl
  bc_right := rfl
  hdf_int := by rw [deriv_const']; exact intervalIntegrable_const
  hdf_diff := by rw [deriv_const']; exact differentiableOn_const 0
  hdf_cont := by rw [deriv_const']; exact continuousOn_const
  hddf_int := by rw [deriv_const', deriv_const']; exact intervalIntegrable_const

/-- `(zero).f x = 0` (definitional). -/
theorem zero_f_eq (x : ℝ) : (zero : H2 L).f x = 0 := rfl

/-! ### Instances -/

/-- `Add (H2 L)`, available once `0 < L` is known as a `Fact`. -/
instance instAdd [Fact (0 < L)] : Add (H2 L) := ⟨add Fact.out⟩

/-- `SMul ℝ (H2 L)`. -/
instance instSMul : SMul ℝ (H2 L) := ⟨smul⟩

/-- `Zero (H2 L)`. -/
instance instZero : Zero (H2 L) := ⟨zero⟩

/-- `u + v = add hL u v` for any proof `hL` (proof irrelevance). -/
theorem add_def [Fact (0 < L)] (hL : 0 < L) (u v : H2 L) : u + v = add hL u v := rfl

/-- `c • u = smul c u`. -/
theorem smul_def (c : ℝ) (u : H2 L) : c • u = smul c u := rfl

/-- `(0 : H2 L) = zero`. -/
theorem zero_def : (0 : H2 L) = zero := rfl

end H2

/-! ## Compatibility with the L² embedding -/

namespace H2Algebra

open L2Embedding

variable {L : ℝ}

/-- **`toL2` is additive.** `toL2 hL (H2.add hL u v) = toL2 hL u + toL2 hL v`
in `L²(0,L)`: the two representatives agree on `Icc 0 L`, which carries the
measure `μ L`. -/
theorem toL2_add (hL : 0 < L) (u v : H2 L) :
    toL2 hL (H2.add hL u v) = toL2 hL u + toL2 hL v := by
  unfold toL2
  rw [← MeasureTheory.MemLp.toLp_add]
  apply MeasureTheory.MemLp.toLp_congr
  unfold μ
  refine ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => ?_)
  exact H2.add_f_eq hL u v hx

/-- `toL2_add` for the `+` notation (needs `[Fact (0 < L)]`). -/
theorem toL2_add' [Fact (0 < L)] (hL : 0 < L) (u v : H2 L) :
    toL2 hL (u + v) = toL2 hL u + toL2 hL v :=
  toL2_add hL u v

/-- **`toL2` is homogeneous.** `toL2 hL (c • u) = c • toL2 hL u`. -/
theorem toL2_smul (hL : 0 < L) (c : ℝ) (u : H2 L) :
    toL2 hL (c • u) = c • toL2 hL u := by
  unfold toL2
  rw [← MeasureTheory.MemLp.toLp_const_smul]
  apply MeasureTheory.MemLp.toLp_congr
  exact ae_of_all _ (fun x => rfl)

/-- **`toL2` sends zero to zero.** -/
theorem toL2_zero (hL : 0 < L) : toL2 hL (0 : H2 L) = 0 := by
  unfold toL2
  rw [← MeasureTheory.MemLp.toLp_zero
    (MeasureTheory.MemLp.zero : MeasureTheory.MemLp (0 : ℝ → ℝ) 2 (μ L))]
  apply MeasureTheory.MemLp.toLp_congr
  exact ae_of_all _ (fun x => rfl)

/-- **Bilinearity of the L² pairing, left slot (addition).** -/
theorem inner_toL2_add_left (hL : 0 < L) (u v w : H2 L) :
    (inner ℝ (toL2 hL (H2.add hL u v)) (toL2 hL w) : ℝ) =
      inner ℝ (toL2 hL u) (toL2 hL w) + inner ℝ (toL2 hL v) (toL2 hL w) := by
  rw [toL2_add, inner_add_left]

/-- **Bilinearity of the L² pairing, left slot (scalars).** -/
theorem inner_toL2_smul_left (hL : 0 < L) (c : ℝ) (u w : H2 L) :
    (inner ℝ (toL2 hL (c • u)) (toL2 hL w) : ℝ) = c * inner ℝ (toL2 hL u) (toL2 hL w) := by
  rw [toL2_smul, real_inner_smul_left]

/-- **Bilinearity of the L² pairing, right slot (addition).** -/
theorem inner_toL2_add_right (hL : 0 < L) (u v w : H2 L) :
    (inner ℝ (toL2 hL w) (toL2 hL (H2.add hL u v)) : ℝ) =
      inner ℝ (toL2 hL w) (toL2 hL u) + inner ℝ (toL2 hL w) (toL2 hL v) := by
  rw [toL2_add, inner_add_right]

/-- The same additivity read through `inner_toL2` as interval integrals:
`∫₀ᴸ (u+v)·w = ∫₀ᴸ u·w + ∫₀ᴸ v·w`. -/
theorem integral_add_mul (hL : 0 < L) (u v w : H2 L) :
    ∫ x in (0)..L, (H2.add hL u v).f x * w.f x =
      (∫ x in (0)..L, u.f x * w.f x) + ∫ x in (0)..L, v.f x * w.f x := by
  rw [← inner_toL2, ← inner_toL2, ← inner_toL2]
  exact inner_toL2_add_left hL u v w

end H2Algebra

end
