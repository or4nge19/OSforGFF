import OSforGFF.GFF.PackageOS1
import OSforGFF.GFF.ComplexCharacteristic
import OSforGFF.CovarianceMomentum
import OSforGFF.CovarianceImaginaryL2Bound

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT
open scoped BigOperators

noncomputable section

variable (m : ℝ) [Fact (0 < m)]

namespace PackageOS1

variable (P : PackageOS1 (m := m))

/-- A purely analytic inequality used in the OS1 bound:
`exp(-½ Re C(f,f)) ≤ exp(½ Re C(Im f, Im f))`.

This depends only on the algebra of `freeCovarianceℂ_bilinear` and the real/imaginary
decomposition of complex test functions. -/
lemma exp_neg_half_re_freeCovariance_self_le_exp_half_re_imaginary (f : TestFunctionℂ) :
    Real.exp (-(1 / 2 : ℝ) * (freeCovarianceℂ_bilinear m f f).re) ≤
      Real.exp ((1 / 2 : ℝ) *
        (freeCovarianceℂ_bilinear m (toComplex (complex_testfunction_decompose f).2)
          (toComplex (complex_testfunction_decompose f).2)).re) := by
  -- Monotonicity of exp reduces to an inequality on exponents.
  apply Real.exp_le_exp.mpr
  set fIm := (complex_testfunction_decompose f).2
  set fRe := (complex_testfunction_decompose f).1
  suffices h :
      -(freeCovarianceℂ_bilinear m f f).re ≤
        (freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm)).re by
    linarith
  -- Write f = fRe + I•fIm and expand C(f,f).
  let frC := toComplex fRe
  let fiC := toComplex fIm
  have hf : f = frC + Complex.I • fiC := by
    ext x
    simpa [frC, fiC, toComplex_apply, smul_eq_mul, complex_testfunction_decompose]
      using complex_testfunction_decompose_recompose f x
  have h_expand : freeCovarianceℂ_bilinear m f f =
      freeCovarianceℂ_bilinear m frC frC + Complex.I * freeCovarianceℂ_bilinear m frC fiC +
        Complex.I * freeCovarianceℂ_bilinear m fiC frC - freeCovarianceℂ_bilinear m fiC fiC := by
    calc
      freeCovarianceℂ_bilinear m f f
          = freeCovarianceℂ_bilinear m (frC + Complex.I • fiC) (frC + Complex.I • fiC) := by
              simpa [hf]
      _ = freeCovarianceℂ_bilinear m frC (frC + Complex.I • fiC) +
            freeCovarianceℂ_bilinear m (Complex.I • fiC) (frC + Complex.I • fiC) := by
            simpa using (freeCovarianceℂ_bilinear_add_left (m := m) (f₁ := frC) (f₂ := Complex.I • fiC)
              (g := frC + Complex.I • fiC))
      _ = freeCovarianceℂ_bilinear m frC frC + freeCovarianceℂ_bilinear m frC (Complex.I • fiC) +
            (freeCovarianceℂ_bilinear m (Complex.I • fiC) frC +
              freeCovarianceℂ_bilinear m (Complex.I • fiC) (Complex.I • fiC)) := by
            simp [freeCovarianceℂ_bilinear_add_right, add_assoc, add_left_comm, add_comm]
      _ = freeCovarianceℂ_bilinear m frC frC + Complex.I * freeCovarianceℂ_bilinear m frC fiC +
            Complex.I * freeCovarianceℂ_bilinear m fiC frC - freeCovarianceℂ_bilinear m fiC fiC := by
            -- pull out scalar factors and use I^2 = -1
            simp only [freeCovarianceℂ_bilinear_smul_right, freeCovarianceℂ_bilinear_smul_left]
            rw [show Complex.I * (Complex.I * freeCovarianceℂ_bilinear m fiC fiC) =
                  -(freeCovarianceℂ_bilinear m fiC fiC) by
                    rw [← mul_assoc, Complex.I_mul_I]; ring]
            ring
  have h_re :
      (freeCovarianceℂ_bilinear m f f).re =
        (freeCovarianceℂ_bilinear m frC frC).re - (freeCovarianceℂ_bilinear m fiC fiC).re := by
    rw [h_expand]
    -- cross terms are purely imaginary because they agree with a real covariance on real inputs
    have h_im_zero : (freeCovarianceℂ_bilinear m frC fiC).im = 0 := by
      have h := QFT.freeCovarianceℂ_bilinear_agrees_on_reals (m := m) fRe fIm
      simpa [frC, fiC, Complex.ofReal_im] using congrArg Complex.im h
    have h_im_zero' : (freeCovarianceℂ_bilinear m fiC frC).im = 0 := by
      have : freeCovarianceℂ_bilinear m fiC frC = freeCovarianceℂ_bilinear m frC fiC :=
        freeCovarianceℂ_bilinear_symm m fiC frC
      simpa [this] using h_im_zero
    simp [h_im_zero, h_im_zero', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have h_pos : 0 ≤ (freeCovarianceℂ_bilinear m frC frC).re := by
    have heq : freeCovarianceℂ_bilinear m frC frC = freeCovarianceℂ m frC frC := by
      unfold freeCovarianceℂ_bilinear freeCovarianceℂ
      congr 1
      ext x
      congr 1
      ext y
      have : starRingEnd ℂ (frC y) = frC y := by
        simp [frC, toComplex_apply]
      rw [this]
    rw [heq]
    exact freeCovarianceℂ_positive m frC
  -- Rearrange: -(Re C(fr,fr) - Re C(fi,fi)) ≤ Re C(fi,fi) using h_pos.
  -- i.e. -Re C(fr,fr) + Re C(fi,fi) ≤ Re C(fi,fi).
  -- so it suffices that -Re C(fr,fr) ≤ 0.
  rw [h_re]
  linarith

/-- The key OS1 exponential bound for the package measure, using only:
1. the complex characteristic functional (from `PackageOS0` + OS0), and
2. a Fourier/Plancherel bound on the free covariance form. -/
lemma generating_L2_bound (f : TestFunctionℂ) :
    ‖GJGeneratingFunctionalℂ P.μ f‖ ≤
      Real.exp ((1 / (2 * m ^ 2)) * ∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume) := by
  -- Start from the package-parametric complex characteristic functional.
  have h_char := PackageOS0.gff_complex_characteristic_OS0 (m := m) (P := P.toPackageOS0) f
  -- Take norms.
  have h_norm :
      ‖GJGeneratingFunctionalℂ P.μ f‖ =
        Real.exp (-(1 / 2 : ℝ) * (freeCovarianceℂ_bilinear m f f).re) := by
    -- Z[f] = exp(-(1/2) * C(f,f)).
    -- ‖exp(z)‖ = exp(Re z).
    rw [h_char, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re]
    norm_num
  -- Bound by the imaginary part, then by the L² bound.
  rw [h_norm]
  have h1 := exp_neg_half_re_freeCovariance_self_le_exp_half_re_imaginary (m := m) f
  have h2 :
      (freeCovarianceℂ_bilinear m (toComplex (complex_testfunction_decompose f).2)
        (toComplex (complex_testfunction_decompose f).2)).re ≤
          (1 / m ^ 2) * ∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume := by
    -- This is a purely analytic momentum-space estimate.
    simpa [pow_two] using (OSforGFF.covariance_imaginary_L2_bound (m := m) f)
  -- Combine, using monotonicity of exp.
  have h_exp_mono :
      Real.exp ((1 / 2 : ℝ) *
        (freeCovarianceℂ_bilinear m (toComplex (complex_testfunction_decompose f).2)
          (toComplex (complex_testfunction_decompose f).2)).re)
        ≤
        Real.exp ((1 / 2 : ℝ) * ((1 / m ^ 2) * ∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume)) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h2 (by norm_num))
  have := le_trans h1 h_exp_mono
  -- algebraic simplification of constants
  simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using this

/-- Package-parametric OS1 regularity for the free field: the bound comes from the complex
characteristic functional and analytic covariance estimates; the (p=2) two-point integrability
obligation is supplied as a package field. -/
theorem os1 : OS1_Regularity P.μ := by
  refine ⟨(2 : ℝ), (1 / (2 * m ^ 2)), by norm_num, by norm_num, ?_, ?_, ?_⟩
  · have hmpos : 0 < m := Fact.out
    have hm2pos : 0 < m ^ 2 := by simpa [pow_two] using sq_pos_of_pos hmpos
    have : 0 < 2 * m ^ 2 := by nlinarith
    exact one_div_pos.mpr this
  · intro f
    have hL2 := generating_L2_bound (m := m) (P := P) f
    -- Strengthen by adding the nonnegative L¹ term.
    have hI1_nonneg : 0 ≤ ∫ x, ‖f x‖ ∂volume := by
      exact integral_nonneg (fun _ => norm_nonneg _)
    have hc_nonneg : 0 ≤ (1 / (2 * m ^ 2) : ℝ) := by
      have hmpos : 0 < m := Fact.out
      have hm2pos : 0 < m ^ 2 := by simpa [pow_two] using sq_pos_of_pos hmpos
      have : 0 < 2 * m ^ 2 := by nlinarith
      exact le_of_lt (one_div_pos.mpr this)
    have hmono :
        (1 / (2 * m ^ 2)) * ∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume ≤
          (1 / (2 * m ^ 2)) * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume) := by
      have hadd : 0 ≤ (1 / (2 * m ^ 2)) * ∫ x, ‖f x‖ ∂volume := mul_nonneg hc_nonneg hI1_nonneg
      calc
        (1 / (2 * m ^ 2)) * ∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume
            ≤ (1 / (2 * m ^ 2)) * ∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume +
              (1 / (2 * m ^ 2)) * ∫ x, ‖f x‖ ∂volume := le_add_of_nonneg_right hadd
        _ = (1 / (2 * m ^ 2)) *
              (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume) := by
              ring
    exact le_trans hL2 (Real.exp_le_exp.mpr hmono)
  · intro hp2
    -- We chose p = 2; satisfy the obligation with the package field.
    simpa using P.twoPointIntegrable

end PackageOS1

end
end GFF
end OSforGFF
