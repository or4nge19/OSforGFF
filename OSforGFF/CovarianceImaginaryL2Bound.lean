import OSforGFF.Covariance
import OSforGFF.CovarianceMomentum
import OSforGFF.CovarianceR
import OSforGFF.ComplexTestFunction

namespace OSforGFF

open MeasureTheory Complex QFT
open scoped BigOperators SchwartzMap

noncomputable section

/-
The covariance of the imaginary part is bounded by (1/m²) times the L² norm squared.
This uses the momentum space representation and the bound 1/(‖k‖² + m²) ≤ 1/m²,
plus Plancherel and the pointwise bound |Im f| ≤ ‖f‖.
-/
lemma covariance_imaginary_L2_bound (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    (freeCovarianceℂ_bilinear m (toComplex (complex_testfunction_decompose f).2)
        (toComplex (complex_testfunction_decompose f).2)).re ≤
      (1 / m ^ 2) * ∫ x, ‖f x‖ ^ 2 ∂volume := by
  -- Abbreviations
  set fIm := (complex_testfunction_decompose f).2
  set F := (SchwartzMap.fourierTransformCLM ℂ (toComplex fIm))

  -- Parseval: real part of the covariance equals the momentum-space integral
  have h_parsevalC :
      (freeCovarianceℂ m (toComplex fIm) (toComplex fIm)).re
        = ∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ (toComplex fIm)) k‖ ^ 2 *
            freePropagatorMomentum_mathlib m k ∂volume := by
    change
      (∫ x, ∫ y,
            (toComplex fIm x) * (freeCovariance m x y : ℂ) *
              (starRingEnd ℂ (toComplex fIm y))
          ∂volume ∂volume).re
        = ∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ (toComplex fIm)) k‖ ^ 2 *
            freePropagatorMomentum_mathlib m k ∂volume
    exact (parseval_covariance_schwartz_bessel (m := m) (f := toComplex fIm))

  -- For real test functions, complex covariance equals the complex bilinear form
  have h_eq_bilin :
      freeCovarianceℂ m (toComplex fIm) (toComplex fIm)
        = freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm) :=
    QFT.freeCovarianceℂ_eq_bilinear_on_reals m fIm fIm

  have h_re_eq :
      (freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm)).re
        = ∫ k, ‖F k‖ ^ 2 * freePropagatorMomentum_mathlib m k ∂volume := by
    simpa [h_eq_bilin, F] using h_parsevalC

  -- Bound the propagator: 1/((2π)²‖k‖² + m²) ≤ 1/m²
  have h_bound : ∀ k, freePropagatorMomentum_mathlib m k ≤ 1 / m ^ 2 := by
    intro k
    unfold freePropagatorMomentum_mathlib
    have hmpos : 0 < m := Fact.out
    have hm2pos : 0 < m ^ 2 := by simpa [pow_two] using sq_pos_of_pos hmpos
    have hden : m ^ 2 ≤ (2 * Real.pi) ^ 2 * ‖k‖ ^ 2 + m ^ 2 := by
      have : 0 ≤ (2 * Real.pi) ^ 2 * ‖k‖ ^ 2 := by positivity
      linarith
    have := one_div_le_one_div_of_le (a := m ^ 2)
      (b := (2 * Real.pi) ^ 2 * ‖k‖ ^ 2 + m ^ 2) (by exact hm2pos) hden
    simpa [one_div] using this

  -- Show integrability of ‖F‖² via MemLp → Integrable (square norm)
  have hF_memLp : MemLp F 2 volume := F.memLp 2 volume
  have hF_meas : AEStronglyMeasurable F volume := hF_memLp.1
  have hF_sq_int : Integrable (fun k => ‖F k‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hF_meas).1 hF_memLp

  -- Pull out the (1/m²) bound from the integral
  have h_dom_int : Integrable (fun k => (1 / m ^ 2) * ‖F k‖ ^ 2) volume :=
    Integrable.const_mul hF_sq_int (1 / m ^ 2)

  have h_nonneg : ∀ k, 0 ≤ ‖F k‖ ^ 2 * freePropagatorMomentum_mathlib m k := by
    intro k
    exact mul_nonneg (by positivity)
      (by
        unfold freePropagatorMomentum_mathlib
        positivity)

  have h_le_pt :
      ∀ k, ‖F k‖ ^ 2 * freePropagatorMomentum_mathlib m k ≤ (1 / m ^ 2) * ‖F k‖ ^ 2 := by
    intro k
    have := mul_le_mul_of_nonneg_left (h_bound k) (by positivity : 0 ≤ ‖F k‖ ^ 2)
    simpa [mul_comm] using this

  have h_int_le :
      ∫ k, ‖F k‖ ^ 2 * freePropagatorMomentum_mathlib m k ∂volume
        ≤ ∫ k, (1 / m ^ 2) * ‖F k‖ ^ 2 ∂volume := by
    exact real_integral_mono_of_le (μ := volume)
      (f := fun k => ‖F k‖ ^ 2 * freePropagatorMomentum_mathlib m k)
      (g := fun k => (1 / m ^ 2) * ‖F k‖ ^ 2)
      h_dom_int h_nonneg h_le_pt

  have h_weight_pull :
      ∫ k, ‖F k‖ ^ 2 * freePropagatorMomentum_mathlib m k ∂volume ≤
        (1 / m ^ 2) * ∫ k, ‖F k‖ ^ 2 ∂volume := by
    have h_const_pull :
        ∫ k, (1 / m ^ 2) * ‖F k‖ ^ 2 ∂volume =
          (1 / m ^ 2) * ∫ k, ‖F k‖ ^ 2 ∂volume := by
      have :
          ∫ k, (m ^ 2)⁻¹ * ‖F k‖ ^ 2 ∂volume =
            (m ^ 2)⁻¹ * ∫ k, ‖F k‖ ^ 2 ∂volume := by
        simpa using (MeasureTheory.integral_const_mul (m ^ 2)⁻¹ (fun k => ‖F k‖ ^ 2))
      simpa [div_eq_mul_inv, mul_assoc] using this
    calc
      ∫ k, ‖F k‖ ^ 2 * freePropagatorMomentum_mathlib m k ∂volume
          ≤ ∫ k, (1 / m ^ 2) * ‖F k‖ ^ 2 ∂volume := h_int_le
      _ = (1 / m ^ 2) * ∫ k, ‖F k‖ ^ 2 ∂volume := h_const_pull

  have h_cov_le :
      (freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm)).re ≤
        (1 / m ^ 2) * (∫ k, ‖F k‖ ^ 2 ∂volume) := by
    simpa [h_re_eq] using h_weight_pull

  -- Plancherel: ∫‖F‖² = ∫‖toComplex fIm‖²
  have h_plancherel :
      ∫ k, ‖F k‖ ^ 2 ∂volume = ∫ x, ‖(toComplex fIm) x‖ ^ 2 ∂volume := by
    simpa [F] using (SchwartzMap.integral_norm_sq_fourier (toComplex fIm))

  -- Pointwise bound: ‖Im f‖ ≤ ‖f‖ ⇒ squares and integrals obey same inequality
  have h_im_pointwise : ∀ x, ‖(toComplex fIm) x‖ ^ 2 ≤ ‖f x‖ ^ 2 := by
    intro x
    -- Rewrite the LHS as |Im(f x)| and square.
    have hL : ‖(toComplex fIm) x‖ = |(f x).im| := by
      simp [toComplex_apply, fIm, complex_testfunction_decompose]
    -- Robust proof without relying on a dedicated lemma name.
    have habs_sq : |(f x).im| ^ 2 = ((f x).im) ^ 2 := by
      simp [pow_two]
    have hineq : ((f x).im) ^ 2 ≤ (f x).re ^ 2 + (f x).im ^ 2 :=
      le_add_of_nonneg_left (sq_nonneg _)
    have hnorm_sq : ‖f x‖ ^ 2 = (f x).re ^ 2 + (f x).im ^ 2 := by
      simpa [Complex.normSq_apply, pow_two] using (Complex.sq_norm (f x))
    have hsq : |(f x).im| ^ 2 ≤ ‖f x‖ ^ 2 := by
      simpa [habs_sq, hnorm_sq] using hineq
    simpa [hL] using hsq

  have hIm_memLp : MemLp (toComplex fIm) 2 volume := (toComplex fIm).memLp 2 volume
  have hIm_meas : AEStronglyMeasurable (toComplex fIm) volume := hIm_memLp.1
  have hIm_sq_int : Integrable (fun x => ‖(toComplex fIm) x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hIm_meas).1 hIm_memLp

  have hf_memLp : MemLp f 2 volume := f.memLp 2 volume
  have hf_meas : AEStronglyMeasurable f volume := hf_memLp.1
  have hf_sq_int : Integrable (fun x => ‖f x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hf_meas).1 hf_memLp

  have h_imag_bound :
      ∫ x, ‖(toComplex fIm) x‖ ^ 2 ∂volume ≤ ∫ x, ‖f x‖ ^ 2 ∂volume := by
    exact real_integral_mono_of_le (μ := volume)
      (f := fun x => ‖(toComplex fIm) x‖ ^ 2)
      (g := fun x => ‖f x‖ ^ 2)
      hf_sq_int (fun x => by positivity) (fun x => by simpa using h_im_pointwise x)

  -- Final chain of inequalities
  calc
    (freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm)).re
        ≤ (1 / m ^ 2) * (∫ k, ‖F k‖ ^ 2 ∂volume) := h_cov_le
    _ = (1 / m ^ 2) * ∫ x, ‖(toComplex fIm) x‖ ^ 2 ∂volume := by
        simp [h_plancherel]
    _ ≤ (1 / m ^ 2) * ∫ x, ‖f x‖ ^ 2 ∂volume := by
        exact mul_le_mul_of_nonneg_left h_imag_bound (by positivity)

end
end OSforGFF
