import Mathlib

noncomputable section

namespace FleetTangentBound

lemma norm_sin_sq (z : ℂ) :
    ‖Complex.sin z‖^2 = (Real.sin z.re)^2 + (Real.sinh z.im)^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.sin_eq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.sin_ofReal_re, Complex.cos_ofReal_re,
    Complex.sin_ofReal_im, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re, Complex.sinh_ofReal_im, Complex.cosh_ofReal_im,
    Complex.I_re, Complex.I_im]
  have ht := Real.sin_sq_add_cos_sq z.re
  have hh := Real.cosh_sq_sub_sinh_sq z.im
  nlinarith [sq_nonneg (Real.sin z.re), sq_nonneg (Real.sinh z.im)]

lemma norm_cos_sq (z : ℂ) :
    ‖Complex.cos z‖^2 = (Real.cos z.re)^2 + (Real.sinh z.im)^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.cos_eq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.sin_ofReal_re, Complex.cos_ofReal_re,
    Complex.sin_ofReal_im, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re, Complex.sinh_ofReal_im, Complex.cosh_ofReal_im,
    Complex.I_re, Complex.I_im]
  have ht := Real.sin_sq_add_cos_sq z.re
  have hh := Real.cosh_sq_sub_sinh_sq z.im
  nlinarith [sq_nonneg (Real.cos z.re), sq_nonneg (Real.sinh z.im)]

/-- A fixed bound on complex tangent outside the horizontal unit strip. -/
theorem norm_tan_le_two {z : ℂ} (hz : 1 ≤ |z.im|) : ‖Complex.tan z‖ ≤ 2 := by
  have ha : 1 ≤ |Real.sinh z.im| := by
    rw [Real.abs_sinh]
    exact hz.trans (Real.self_le_sinh_iff.mpr (abs_nonneg z.im))
  have hs : 1 ≤ (Real.sinh z.im)^2 := by
    nlinarith [sq_abs (Real.sinh z.im), sq_nonneg (|Real.sinh z.im| - 1)]
  have hc : 0 < ‖Complex.cos z‖ := by
    have he := norm_cos_sq z
    have hn := norm_nonneg (Complex.cos z)
    nlinarith [sq_nonneg (Real.cos z.re)]
  have hb : ‖Complex.sin z‖ ≤ 2 * ‖Complex.cos z‖ := by
    have he := norm_sin_sq z
    have he' := norm_cos_sq z
    have ht := Real.sin_sq_add_cos_sq z.re
    have hn := norm_nonneg (Complex.sin z)
    nlinarith [sq_nonneg (Real.cos z.re), sq_nonneg (‖Complex.sin z‖ - 2*‖Complex.cos z‖)]
  rw [Complex.tan, norm_div]
  exact (div_le_iff₀ hc).mpr hb

/-- The tangent factor occurring in the gamma kernel is uniformly bounded for |t|≥1. -/
theorem norm_tan_pi_line_le_two (σ t : ℝ) (ht : 1 ≤ |t|) :
    ‖Complex.tan ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖ ≤ 2 := by
  apply norm_tan_le_two
  have he : (((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) / 2)).im =
      Real.pi / 2 * t := by simp; ring
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.pi / 2)]
  have hp : 1 ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
  nlinarith

end FleetTangentBound
