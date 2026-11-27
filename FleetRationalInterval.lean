import FleetElementaryIntervalCertificate
import FleetElementaryNumericalInstances
import Mathlib

/-! Exact rational interval operations for finite numerical certificates.
Every semantic theorem concerns the real value, while the interval endpoints
are computable rationals. No floating-point computation is a proof premise. -/

namespace FleetRationalInterval

structure Box where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def Contains (a : Box) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)

def point (q : ℚ) : Box := ⟨q, q⟩
def add (a b : Box) : Box := ⟨a.lo+b.lo, a.hi+b.hi⟩
def neg (a : Box) : Box := ⟨-a.hi, -a.lo⟩
def sub (a b : Box) : Box := add a (neg b)

theorem point_contains (q : ℚ) : Contains (point q) q := ⟨le_rfl, le_rfl⟩

theorem add_contains {a b : Box} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (add a b) (x+y) := by
  unfold Contains add at *
  push_cast
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem neg_contains {a : Box} {x : ℝ} (hx : Contains a x) :
    Contains (neg a) (-x) := by
  unfold Contains neg at *
  push_cast
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem sub_contains {a b : Box} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (sub a b) (x-y) := add_contains hx (neg_contains hy)

def square (a : Box) : Box :=
  ⟨if 0 ≤ a.lo then a.lo^2 else if a.hi ≤ 0 then a.hi^2 else 0,
    max (a.lo^2) (a.hi^2)⟩

theorem square_contains {a : Box} {x : ℝ} (hx : Contains a x) :
    Contains (square a) (x^2) := by
  unfold Contains at hx ⊢
  constructor
  · unfold square
    simp only
    split_ifs with hl hu
    · have hl' : (0 : ℝ) ≤ a.lo := by exact_mod_cast hl
      push_cast
      exact pow_le_pow_left₀ hl' hx.1 2
    · have hu' : (a.hi : ℝ) ≤ 0 := by exact_mod_cast hu
      push_cast
      nlinarith [sq_nonneg (x-(a.hi : ℝ))]
    · norm_num
      positivity
  · simp only [square, Rat.cast_max, Rat.cast_pow]
    by_cases h : 0 ≤ x
    · exact (pow_le_pow_left₀ h hx.2 2).trans (le_max_right _ _)
    · have h' : x ≤ 0 := le_of_not_ge h
      apply le_trans _ (le_max_left _ _)
      nlinarith [sq_nonneg ((a.lo : ℝ)-x)]

private theorem product_upper {a b c d x y m : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hac : a*c ≤ m) (had : a*d ≤ m) (hbc : b*c ≤ m) (hbd : b*d ≤ m) :
    x*y ≤ m := by
  by_cases h : 0 ≤ x
  · have hxy : x*y ≤ x*d := mul_le_mul_of_nonneg_left hy.2 h
    by_cases hd : 0 ≤ d
    · exact (hxy.trans (mul_le_mul_of_nonneg_right hx.2 hd)).trans hbd
    · exact (hxy.trans (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hd))).trans had
  · have hxy : x*y ≤ x*c := mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge h)
    by_cases hc : 0 ≤ c
    · exact (hxy.trans (mul_le_mul_of_nonneg_right hx.2 hc)).trans hbc
    · exact (hxy.trans (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hc))).trans hac

def mul (a b : Box) : Box :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩

theorem mul_contains {a b : Box} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (mul a b) (x*y) := by
  unfold Contains at hx hy ⊢
  simp only [mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  constructor
  · have hh := product_upper
      (show -(a.hi : ℝ) ≤ -x ∧ -x ≤ -(a.lo : ℝ) from ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩)
      hy
      (m := -min (min ((a.lo : ℝ)*b.lo) ((a.lo : ℝ)*b.hi))
        (min ((a.hi : ℝ)*b.lo) ((a.hi : ℝ)*b.hi)))
    have h1 := min_le_left ((a.lo : ℝ)*b.lo) ((a.lo : ℝ)*b.hi)
    have h2 := min_le_right ((a.lo : ℝ)*b.lo) ((a.lo : ℝ)*b.hi)
    have h3 := min_le_left ((a.hi : ℝ)*b.lo) ((a.hi : ℝ)*b.hi)
    have h4 := min_le_right ((a.hi : ℝ)*b.lo) ((a.hi : ℝ)*b.hi)
    have h5 := min_le_left (min ((a.lo : ℝ)*b.lo) ((a.lo : ℝ)*b.hi))
      (min ((a.hi : ℝ)*b.lo) ((a.hi : ℝ)*b.hi))
    have h6 := min_le_right (min ((a.lo : ℝ)*b.lo) ((a.lo : ℝ)*b.hi))
      (min ((a.hi : ℝ)*b.lo) ((a.hi : ℝ)*b.hi))
    have hbound := hh (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · apply product_upper hx hy
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

def invPositive (a : Box) : Box := ⟨a.hi⁻¹, a.lo⁻¹⟩

theorem invPositive_contains {a : Box} {x : ℝ} (ha : 0 < a.lo) (hx : Contains a x) :
    Contains (invPositive a) x⁻¹ := by
  have ha' : (0 : ℝ) < a.lo := by exact_mod_cast ha
  have hx' := ha'.trans_le hx.1
  have hb' := hx'.trans_le hx.2
  unfold Contains invPositive
  push_cast
  exact ⟨(inv_le_inv₀ hb' hx').mpr hx.2, (inv_le_inv₀ hx' ha').mpr hx.1⟩

def roundDown (q : ℚ) : ℚ := (⌊q * 1000000000000⌋ : ℤ) / 1000000000000
def roundUp (q : ℚ) : ℚ := -roundDown (-q)
def rounded (a : Box) : Box := ⟨roundDown a.lo, roundUp a.hi⟩

theorem roundDown_le (q : ℚ) : roundDown q ≤ q := by
  unfold roundDown
  apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 1000000000000)).mpr
  exact Int.floor_le _

theorem le_roundUp (q : ℚ) : q ≤ roundUp q := by
  have h := roundDown_le (-q)
  unfold roundUp
  linarith

theorem rounded_contains {a : Box} {x : ℝ} (hx : Contains a x) :
    Contains (rounded a) x := by
  have hl : (roundDown a.lo : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast roundDown_le a.lo
  have hu : (a.hi : ℝ) ≤ (roundUp a.hi : ℝ) := by exact_mod_cast le_roundUp a.hi
  exact ⟨hl.trans hx.1, hx.2.trans hu⟩

def expSeed (q : ℚ) : Box :=
  let p := FleetElementaryIntervalCertificate.expPolynomial 12 q
  let r := FleetElementaryIntervalCertificate.expRemainder 12 q
  ⟨p-r, p+r⟩

theorem expSeed_contains (q : ℚ) (hq : |q| ≤ 1) :
    Contains (expSeed q) (Real.exp q) := by
  exact FleetElementaryIntervalCertificate.exp_small (by norm_num) hq le_rfl le_rfl

def repeatedSquare : ℕ → Box → Box
  | 0, a => a
  | n+1, a => rounded (square (repeatedSquare n a))

theorem repeatedSquare_exp_contains (n : ℕ) {a : Box} {x : ℝ}
    (ha : Contains a (Real.exp x)) :
    Contains (repeatedSquare n a) (Real.exp ((2:ℝ)^n*x)) := by
  induction n with
  | zero => simpa [repeatedSquare] using ha
  | succ n ih =>
    have h := rounded_contains (square_contains ih)
    have he : Real.exp ((2:ℝ)^n*x)^2 = Real.exp ((2:ℝ)^(n+1)*x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    simpa only [repeatedSquare, he] using h

def expScaled (q : ℚ) : Box := repeatedSquare 8 (rounded (expSeed (q/256)))

theorem expScaled_contains (q : ℚ) (hq : |q| ≤ 256) :
    Contains (expScaled q) (Real.exp q) := by
  have hs : |q/256| ≤ 1 := by rw [abs_div]; norm_num; linarith
  have h := repeatedSquare_exp_contains 8 (rounded_contains (expSeed_contains (q/256) hs))
  norm_num at h
  have he : (256 : ℝ) * ((q : ℝ) / 256) = (q : ℝ) := by ring
  rw [he] at h
  exact h

def expAt (q : ℚ) : Box :=
  if q < -144 then ⟨0, 1/10^24⟩ else expScaled q

theorem expAt_contains (q : ℚ) (hq : q ≤ 256) :
    Contains (expAt q) (Real.exp q) := by
  unfold expAt
  split_ifs with hl
  · have hl' : (q : ℝ) ≤ -144 := by exact_mod_cast hl.le
    refine ⟨by simpa using (Real.exp_pos (q:ℝ)).le, ?_⟩
    have h := (Real.exp_le_exp.mpr hl').trans FleetElementaryNumericalInstances.exp_neg_144_le
    norm_num at h ⊢
    exact h
  · exact expScaled_contains q (abs_le.mpr ⟨by linarith, hq⟩)

def expInterval (a : Box) : Box := ⟨(expAt a.lo).lo, (expAt a.hi).hi⟩

theorem expInterval_contains {a : Box} {x : ℝ} (ha : a.hi ≤ 256) (hx : Contains a x) :
    Contains (expInterval a) (Real.exp x) := by
  have hab : a.lo ≤ a.hi := by exact_mod_cast hx.1.trans hx.2
  exact ⟨(expAt_contains a.lo (hab.trans ha)).1.trans (Real.exp_le_exp.mpr hx.1),
    (Real.exp_le_exp.mpr hx.2).trans (expAt_contains a.hi ha).2⟩

theorem enlarge {a b : Box} {x : ℝ} (hx : Contains a x)
    (hl : b.lo ≤ a.lo) (hu : a.hi ≤ b.hi) : Contains b x := by
  have hl' : (b.lo : ℝ) ≤ a.lo := by exact_mod_cast hl
  have hu' : (a.hi : ℝ) ≤ b.hi := by exact_mod_cast hu
  exact ⟨hl'.trans hx.1, hx.2.trans hu'⟩

/-- Interval bisection retains the old enclosure when an exponential
comparison overlaps; an inconclusive comparison never becomes an assertion. -/
def logBisect : ℕ → ℚ → Box → Box
  | 0, _, a => a
  | n+1, q, a =>
    let mid := (a.lo+a.hi)/2
    if (expAt mid).hi ≤ q then logBisect n q ⟨mid, a.hi⟩
    else if q ≤ (expAt mid).lo then logBisect n q ⟨a.lo, mid⟩
    else a

theorem logBisect_contains (n : ℕ) {q : ℚ} {a : Box}
    (hq : 0 < q) (ha : a.hi ≤ 16) (hx : Contains a (Real.log q)) :
    Contains (logBisect n q a) (Real.log q) := by
  induction n generalizing a with
  | zero => exact hx
  | succ n ih =>
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hab : a.lo ≤ a.hi := by exact_mod_cast hx.1.trans hx.2
    have hm : (a.lo+a.hi)/2 ≤ a.hi := by linarith
    have he := expAt_contains ((a.lo+a.hi)/2) (show (a.lo+a.hi)/2 ≤ 256 by linarith)
    unfold logBisect
    dsimp only
    split_ifs with hl hu
    · apply ih (a := ⟨(a.lo+a.hi)/2, a.hi⟩) ha
      refine ⟨?_, hx.2⟩
      apply (Real.le_log_iff_exp_le hq').mpr
      exact he.2.trans (by exact_mod_cast hl)
    · apply ih (a := ⟨a.lo, (a.lo+a.hi)/2⟩) (hm.trans ha)
      refine ⟨hx.1, ?_⟩
      apply (Real.log_le_iff_le_exp hq').mpr
      exact (show (q : ℝ) ≤ ((expAt ((a.lo+a.hi)/2)).lo : ℝ) by exact_mod_cast hu).trans he.1
    · exact hx

def logAt (q : ℚ) : Box := logBisect 24 q ⟨0,16⟩

theorem logAt_contains (q : ℚ) (hq : 1 ≤ q) (hQ : q ≤ 65536) :
    Contains (logAt q) (Real.log q) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hq'
  have he : (65536 : ℝ) ≤ Real.exp 16 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (show (2 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 16
    rw [Real.exp_one_pow] at h
    norm_num at h
    exact h
  apply logBisect_contains 24 (by linarith) (by norm_num)
  refine ⟨by simpa using Real.log_nonneg hq', ?_⟩
  apply (Real.log_le_iff_le_exp hq0).mpr
  exact (show (q : ℝ) ≤ 65536 by exact_mod_cast hQ).trans he

def logInterval (a : Box) : Box := ⟨(logAt a.lo).lo, (logAt a.hi).hi⟩

theorem logInterval_contains {a : Box} {x : ℝ} (hl : 1 ≤ a.lo) (hu : a.hi ≤ 65536)
    (hx : Contains a x) : Contains (logInterval a) (Real.log x) := by
  have hab : a.lo ≤ a.hi := by exact_mod_cast hx.1.trans hx.2
  have hpos : (0 : ℝ) < a.lo := by exact_mod_cast (show (0 : ℚ) < a.lo by linarith)
  exact ⟨(logAt_contains a.lo hl (hab.trans hu)).1.trans (Real.log_le_log hpos hx.1),
    (Real.log_le_log (hpos.trans_le hx.1) hx.2).trans (logAt_contains a.hi (hl.trans hab) hu).2⟩

end FleetRationalInterval
