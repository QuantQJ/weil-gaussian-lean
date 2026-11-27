import FleetSignUncertaintyCert1
import FleetSignUncertaintyCert2
import FleetSignUncertaintyCert3

/-!
# Sign uncertainty: the certified bound

The `+1` sign uncertainty constant (Bourgain–Clozel–Kahane, dimension one; problem 11 of the
AlphaEvolve repository of problems) satisfies `signUncertaintyConstant ≤ 7887/(2π·4096) ≈ 0.3064587`.

Witness: `f(x) = Q(2πx²) e^{-πx²}` with `Q = hornerTP sigR` (data in `FleetSignUncertaintyData`,
201 eigen-coefficients, `deg Q = 400`); `f̂ = f` by `eig_hornerTP`, `f(0) = Q(0) < 0` by `sig_zero`,
and `Q > 0` on `[7887/4096, ∞)` by `sig_pos`, assembled from the kernel-checked Descartes-leaf chunks
`sigLeaves*` and the tail certificate `sigTail`.
-/

namespace FleetSignUncertainty

open Real

/-- `Q > 0` on `[7887/4096, ∞)`. -/
theorem sig_pos : ∀ t : ℝ, ((7887 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ t →
    0 < evalP ((sigP, sigN) : NP) t := by
  have h48 := chunk_tail sig_length (M := 1) (A := 2074) (by norm_num) sigTail
  have h47 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves47) h48 (by norm_num)
  have h46 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves46) h47 (by norm_num)
  have h45 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves45) h46 (by norm_num)
  have h44 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves44) h45 (by norm_num)
  have h43 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves43) h44 (by norm_num)
  have h42 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves42) h43 (by norm_num)
  have h41 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves41) h42 (by norm_num)
  have h40 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves40) h41 (by norm_num)
  have h39 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves39) h40 (by norm_num)
  have h38 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves38) h39 (by norm_num)
  have h37 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves37) h38 (by norm_num)
  have h36 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves36) h37 (by norm_num)
  have h35 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves35) h36 (by norm_num)
  have h34 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves34) h35 (by norm_num)
  have h33 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves33) h34 (by norm_num)
  have h32 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves32) h33 (by norm_num)
  have h31 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves31) h32 (by norm_num)
  have h30 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves30) h31 (by norm_num)
  have h29 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves29) h30 (by norm_num)
  have h28 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves28) h29 (by norm_num)
  have h27 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves27) h28 (by norm_num)
  have h26 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves26) h27 (by norm_num)
  have h25 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves25) h26 (by norm_num)
  have h24 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves24) h25 (by norm_num)
  have h23 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves23) h24 (by norm_num)
  have h22 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves22) h23 (by norm_num)
  have h21 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves21) h22 (by norm_num)
  have h20 := pos_glue (chunk_leaves sig_length (M := 1) (by norm_num) (by simp) sigLeaves20) h21 (by norm_num)
  have h19 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves19) h20 (by norm_num)
  have h18 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves18) h19 (by norm_num)
  have h17 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves17) h18 (by norm_num)
  have h16 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves16) h17 (by norm_num)
  have h15 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves15) h16 (by norm_num)
  have h14 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves14) h15 (by norm_num)
  have h13 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves13) h14 (by norm_num)
  have h12 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves12) h13 (by norm_num)
  have h11 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves11) h12 (by norm_num)
  have h10 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves10) h11 (by norm_num)
  have h9 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves9) h10 (by norm_num)
  have h8 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves8) h9 (by norm_num)
  have h7 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves7) h8 (by norm_num)
  have h6 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves6) h7 (by norm_num)
  have h5 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves5) h6 (by norm_num)
  have h4 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves4) h5 (by norm_num)
  have h3 := pos_glue (chunk_leaves sig_length (M := 16) (by norm_num) (by simp) sigLeaves3) h4 (by norm_num)
  have h2 := pos_glue (chunk_leaves sig_length (M := 4096) (by norm_num) (by simp) sigLeaves2) h3 (by norm_num)
  have h1 := pos_glue (chunk_leaves sig_length (M := 4096) (by norm_num) (by simp) sigLeaves1) h2 (by norm_num)
  have h0 := pos_glue (chunk_leaves sig_length (M := 4096) (by norm_num) (by simp) sigLeaves0) h1 (by norm_num)
  exact h0

/-- **Upper bound for the `+1` sign uncertainty constant**: `C ≤ 7887/(2π·4096)`. -/
theorem signUncertaintyConstant_le_cert :
    signUncertaintyConstant ≤ (((7887 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ)) / (2 * π) :=
  bound_of_certificate sigR sigP sigN _ hornerTP_sigR (by norm_num) sig_zero sig_pos

/-- Decimal form: `signUncertaintyConstant < 0.30646`. -/
theorem signUncertaintyConstant_lt : signUncertaintyConstant < 0.30646 := by
  refine lt_of_le_of_lt signUncertaintyConstant_le_cert ?_
  rw [div_lt_iff₀ (by positivity)]
  push_cast
  nlinarith [Real.pi_gt_d6]

end FleetSignUncertainty
