import FleetFullLineArithmetic

noncomputable section
open MeasureTheory Complex
open scoped FourierTransform
namespace FleetFullLineLinearity
open FleetFullLineFourier

lemma h_sub {f g : ℝ → ℂ} (z : ℂ)
    (hf : Integrable (fun u : ℝ => f u*Complex.exp (I*z*(u : ℂ))))
    (hg : Integrable (fun u : ℝ => g u*Complex.exp (I*z*(u : ℂ)))) :
    h (f-g) z = h f z-h g z := by
  unfold h
  simp only [Pi.sub_apply, sub_mul]
  exact integral_sub hf hg

lemma integrable_real_integrand {g : ℝ → ℂ} (hg : Integrable g) (t : ℝ) :
    Integrable (fun u : ℝ => g u*Complex.exp (I*(t : ℂ)*(u : ℂ))) := by
  have hm : AEStronglyMeasurable (fun u : ℝ => g u*Complex.exp (I*(t : ℂ)*(u : ℂ))) :=
    hg.aestronglyMeasurable.mul (by fun_prop : Continuous
      (fun u : ℝ => Complex.exp (I*(t : ℂ)*(u : ℂ)))).aestronglyMeasurable
  apply hg.norm.mono' hm
  filter_upwards [] with u
  rw [norm_mul]
  have he : I*(t : ℂ)*(u : ℂ) = ((t*u : ℝ) : ℂ)*I := by push_cast; ring
  rw [he, Complex.norm_exp_ofReal_mul_I, mul_one]

lemma h_sub_real {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    h (f-g) (t : ℂ) = h f (t : ℂ)-h g (t : ℂ) :=
  h_sub _ (integrable_real_integrand hf t) (integrable_real_integrand hg t)

lemma continuous_h_real {g : ℝ → ℂ} (hg : Integrable g) :
    Continuous (fun t : ℝ => h g (t : ℂ)) := by
  have hc : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by
      fun_prop) hg
  simp_rw [h_eq_fourier]
  exact hc.comp (by fun_prop)

lemma archimedean_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hfA : Integrable (fun t : ℝ => h f (t : ℂ)*(FleetGammaKernel.weight t : ℂ)))
    (hgA : Integrable (fun t : ℝ => h g (t : ℂ)*(FleetGammaKernel.weight t : ℂ))) :
    FleetFullLineArithmetic.archimedean (f-g) =
      FleetFullLineArithmetic.archimedean f-FleetFullLineArithmetic.archimedean g := by
  unfold FleetFullLineArithmetic.archimedean
  simp_rw [h_sub_real hf hg, sub_mul]
  rw [integral_sub hfA hgA, mul_sub]

end FleetFullLineLinearity
