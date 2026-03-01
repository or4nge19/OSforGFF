/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Topology.Constructions

import OSforGFF.Basic
import OSforGFF.OS_Axioms
import OSforGFF.Covariance
import OSforGFF.CovarianceMomentum
import OSforGFF.CovarianceR
import OSforGFF.CovarianceImaginaryL2Bound
import OSforGFF.GFFMconstruct
import OSforGFF.GFFIsGaussian
import OSforGFF.GFF.PackageOS0Proved
import OSforGFF.GFF.PackageOS1
import OSforGFF.GFF.OS1

/-!
# OS1 Regularity Axiom - Complete Theory

This file contains the complete theory supporting the OS1 (Regularity) axiom
from `OS_Axioms.lean`. It provides all the mathematical infrastructure needed
to work with regularity conditions in Euclidean field theory.


## Key Mathematical Results

The OS1 axiom establishes exponential temperedness:
```
‖Z[f]‖ ≤ exp(c(‖f‖_L¹ + ‖f‖_L^p^p))
```
where 1 ≤ p ≤ 2, c > 0, and when p = 2 we require local integrability of the two-point function.

This ensures controlled growth necessary for Osterwalder-Schrader reconstruction.
-/

open MeasureTheory Complex BigOperators SchwartzMap Real QFT
open scoped MeasureTheory ENNReal

/-! ## Axioms

All axioms for this file are collected here for easy reference.
-/

/-- Plancherel (Schwartz): L² norm preservation for the Fourier transform.
    This follows directly from Mathlib's `SchwartzMap.integral_norm_sq_fourier`.
    Mathlib's Fourier transform is unitary-normalized, so no multiplicative constant is needed. -/
theorem fourier_plancherel_schwartz (g : TestFunctionℂ) :
    ∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ g) k‖^2 ∂volume =
      ∫ x, ‖g x‖^2 ∂volume :=
  SchwartzMap.integral_norm_sq_fourier g

/-- **Connection axiom**: The two-point Schwinger function for the GFF equals the
    free covariance kernel. This is the fundamental connection between the abstract
    limit-based definition and the concrete position-space propagator.

    Mathematically: ⟨φ(x)φ(0)⟩_μ = C(x, 0) for the Gaussian measure with covariance C.

    **Justification (no longer an axiom):**
    This follows from the double mollifier convergence theorem. The two-point function
    S₂(x) is defined as the limit of smeared correlations:
      S₂(x) = lim_{ε→0} ∫∫ φ_ε(u-x) ⟨φ(u)φ(v)⟩ φ_ε(v) du dv
            = lim_{ε→0} (φ_ε ⋆ (φ_ε ⋆ C))(x)
            = C(x)   for x ≠ 0

    See `double_mollifier_convergence` in FunctionalAnalysis.lean for the general result.

    Note: The abstract `SchwingerTwoPointFunction` in OS_Axioms.lean is now defined as
    a limit (using `limUnder`), properly avoiding DiracDelta. For the GFF specifically,
    we use this direct definition for computational convenience. -/
noncomputable def SchwingerTwoPointFunction_GFF (m : ℝ) [Fact (0 < m)] (x : SpaceTime) : ℝ :=
  freeCovarianceKernel m x

/-- The GFF two-point function equals the free covariance kernel by definition. -/
theorem schwingerTwoPoint_eq_freeCovarianceKernel (m : ℝ) [Fact (0 < m)] (x : SpaceTime) :
  SchwingerTwoPointFunction_GFF m x = freeCovarianceKernel m x := rfl

/-- Compatibility: The abstract SchwingerTwoPointFunction agrees with the concrete
    definition for the GFF. This uses the limit-based definition of SchwingerTwoPointFunction
    and the double mollifier convergence theorem via `schwingerTwoPointFunction_eq_kernel`.

    The proof requires:
    1. Continuity of freeCovarianceKernel away from 0
    2. SchwingerFunction₂ for the GFF computes ∫∫ f(u) C(u-v) g(v) du dv

    Both are standard properties of the GFF; the sorries encode these standard facts. -/
theorem schwingerTwoPointFunction_eq_GFF (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] (x : SpaceTime) (hx : x ≠ 0) :
  SchwingerTwoPointFunction (gaussianFreeField_free m) x = SchwingerTwoPointFunction_GFF m x := by
  -- Use schwingerTwoPointFunction_eq_kernel
  have h_cont : ContinuousOn (freeCovarianceKernel m) {y : SpaceTime | y ≠ 0} :=
    freeCovarianceKernel_continuousOn m (Fact.elim ‹Fact (0 < m)›)
  have h_S₂ : ∀ (f g : TestFunction),
      SchwingerFunction₂ (gaussianFreeField_free m) f g =
      ∫ u, ∫ v, f u * freeCovarianceKernel m (u - v) * g v := by
    -- Chain: S₂(f,g) = ∫ω (ωf)(ωg) dμ = freeCovarianceFormR m f g = ∫∫ f(u) C(u,v) g(v)
    -- where C(u,v) = freeCovarianceKernel m (u-v) by translation invariance
    intro f g
    -- Step 1: S₂ = ∫ω (ωf)(ωg) via schwinger_eq_covariance
    rw [schwinger_eq_covariance]
    -- Unfold distributionPairing to ω f
    simp only [distributionPairing]
    -- Step 2: For GFF, ∫ω (ωf)(ωg) = freeCovarianceFormR via schwinger_eq_covariance_real
    rw [GFFIsGaussian.schwinger_eq_covariance_real m f g]
    -- Step 3: freeCovarianceFormR = ∫∫ f(u) * freeCovariance(u,v) * g(v)
    unfold freeCovarianceFormR
    -- Step 4: freeCovariance(x,y) = freeCovarianceKernel(x-y) by translation invariance
    congr 1
    ext u
    congr 1
    ext v
    -- The kernel is translation invariant
    have h_transl : freeCovariance m u v = freeCovarianceKernel m (u - v) := by
      simp only [freeCovarianceKernel, freeCovariance, freeCovarianceBessel, zero_sub, norm_neg]
    rw [h_transl]
  -- Apply the general kernel theorem
  rw [schwingerTwoPointFunction_eq_kernel (gaussianFreeField_free m) x hx
        (freeCovarianceKernel m) h_cont h_S₂]
  -- By definition of SchwingerTwoPointFunction_GFF
  rfl

/-- The abstract SchwingerTwoPointFunction equals freeCovarianceKernel for the GFF.
    This is the version needed for downstream proofs using TwoPointIntegrable.
    Note: Only holds for x ≠ 0 since the covariance is undefined at coincident points. -/
theorem schwingerTwoPointFunction_eq_freeCovarianceKernel (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] (x : SpaceTime) (hx : x ≠ 0) :
  SchwingerTwoPointFunction (gaussianFreeField_free m) x = freeCovarianceKernel m x := by
  rw [schwingerTwoPointFunction_eq_GFF m x hx, schwingerTwoPoint_eq_freeCovarianceKernel]

/-- The GFF two-point Schwinger function satisfies a polynomial decay bound.
    For the free field, this follows from the Bessel function asymptotics:
    - Near origin: K₁(mr) ~ 1/(mr), giving decay like 1/r²
    - Far from origin: K₁(mr) ~ exp(-mr), which is even faster decay -/
theorem schwinger_two_point_decay_bound_GFF (m : ℝ) [Fact (0 < m)] :
  ∃ C : ℝ, C > 0 ∧
    ∀ x y : SpaceTime,
      ‖SchwingerTwoPointFunction_GFF m (x - y)‖ ≤
        C * ‖x - y‖ ^ (-2 : ℝ) := by
  obtain ⟨C, hC_pos, hC_bound⟩ := freeCovarianceKernel_decay_bound m (Fact.out)
  refine ⟨C, hC_pos, fun x y => ?_⟩
  -- SchwingerTwoPointFunction_GFF is definitionally equal to freeCovarianceKernel
  rw [schwingerTwoPoint_eq_freeCovarianceKernel]
  -- The norm of a real number is its absolute value
  rw [Real.norm_eq_abs]
  exact hC_bound (x - y)

/-- The abstract two-point Schwinger function satisfies a polynomial decay bound.
    Uses the bridge lemma to connect to the concrete GFF definition.
    Note: At x = y (coincident points), the bound still holds since the abstract
    definition regularizes S(0) = 0 and 0^(-2) = 0 by Mathlib convention. -/
theorem schwinger_two_point_decay_bound (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
  ∃ C : ℝ, C > 0 ∧
    ∀ x y : SpaceTime,
      ‖SchwingerTwoPointFunction (gaussianFreeField_free m) (x - y)‖ ≤
        C * ‖x - y‖ ^ (-2 : ℝ) := by
  obtain ⟨C, hC_pos, hC_bound⟩ := schwinger_two_point_decay_bound_GFF m
  refine ⟨C, hC_pos, fun x y => ?_⟩
  by_cases h : x - y = 0
  · -- At coincident points x = y, both sides are 0
    simp only [h]
    -- By definition, SchwingerTwoPointFunction _ 0 = 0
    rw [schwingerTwoPointFunction_zero]
    -- By mathlib convention, 0^(-2) = 0, so RHS = C * 0 = 0
    have h_rhs : C * (0 : ℝ) ^ (-2 : ℝ) = 0 := by
      rw [Real.zero_rpow (by norm_num : (-2 : ℝ) ≠ 0)]
      ring
    simp only [norm_zero, h_rhs, le_refl]
  · -- Non-coincident points: use the bridge lemma
    rw [schwingerTwoPointFunction_eq_freeCovarianceKernel m (x - y) h]
    rw [Real.norm_eq_abs]
    have := hC_bound x y
    rw [schwingerTwoPoint_eq_freeCovarianceKernel, Real.norm_eq_abs] at this
    exact this

/-- The abstract two-point Schwinger function is measurable.
    This uses the bridge lemma to connect to the concrete GFF definition.
    The functions agree on the complement of {0}, which has full measure. -/
theorem schwingerTwoPoint_measurable (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    AEStronglyMeasurable (fun x => SchwingerTwoPointFunction (gaussianFreeField_free m) x) volume := by
  -- Use that the abstract and concrete definitions agree except possibly at 0
  -- Since {0} is a null set in Lebesgue measure, AE strong measurability follows from
  -- the measurability of freeCovarianceKernel and the fact that the functions differ
  -- only on a null set
  have h_kernel_meas := (freeCovarianceKernel_integrable m (Fact.out)).aestronglyMeasurable
  -- The abstract definition agrees with the kernel on {x ≠ 0}
  have h_ae_eq : (fun x => SchwingerTwoPointFunction (gaussianFreeField_free m) x) =ᶠ[ae volume]
                 freeCovarianceKernel m := by
    -- {0} has measure zero in Lebesgue measure
    have h_singleton_null : (volume : Measure SpaceTime) {(0 : SpaceTime)} = 0 :=
      MeasureTheory.measure_singleton (0 : SpaceTime)
    -- The complement of {0} has full measure, so {x ≠ 0} ∈ ae volume
    have h_mem : {x : SpaceTime | x ≠ 0} ∈ ae volume := by
      rw [MeasureTheory.mem_ae_iff]
      simp only [ne_eq, Set.compl_setOf, not_not]
      exact h_singleton_null
    -- The functions agree on this set
    exact Filter.eventuallyEq_of_mem h_mem (fun x hx => schwingerTwoPointFunction_eq_freeCovarianceKernel m x hx)
  exact AEStronglyMeasurable.congr h_kernel_meas h_ae_eq.symm

/-! ## GFF Exponential Bound

Elementary bound on the GFF generating function using complex exponential properties.
-/

/-- The norm of the GFF generating function equals the exponential of minus one-half
    the real part of the covariance. This is an elementary property of complex exponentials:
    |exp(z)| = exp(Re z). -/
lemma gff_generating_norm_eq (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] (f : TestFunctionℂ) :
  ‖GJGeneratingFunctionalℂ (gaussianFreeField_free m) f‖ =
    Real.exp (-(1/2) * (freeCovarianceℂ_bilinear m f f).re) := by
  rw [gff_complex_generating, gff_two_point_equals_covarianceℂ_free, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re]
  norm_num

/-- Using bilinearity and the real/imaginary decomposition, the real part of C(f,f)
    satisfies Re C(f,f) = C(Re f, Re f) - C(Im f, Im f). Combined with monotonicity
    of exp, this gives the bound exp(-1/2 Re C(f,f)) ≤ exp(1/2 C(Im f, Im f)). -/
lemma gff_generating_bound_by_imaginary (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
  Real.exp (-(1/2) * (freeCovarianceℂ_bilinear m f f).re) ≤
    Real.exp ((1/2) * (freeCovarianceℂ_bilinear m (toComplex (complex_testfunction_decompose f).2)
                                                     (toComplex (complex_testfunction_decompose f).2)).re) := by
  -- Apply monotonicity of exp: it suffices to show -(1/2) Re C(f,f) ≤ (1/2) C(Im f, Im f)
  apply Real.exp_le_exp.mpr
  -- Abbreviate the imaginary and real parts
  set fIm := (complex_testfunction_decompose f).2
  set fRe := (complex_testfunction_decompose f).1
  -- Equivalently: -Re C(f,f) ≤ Re C(toComplex fIm, toComplex fIm)
  suffices h : -(freeCovarianceℂ_bilinear m f f).re ≤
               (freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm)).re by linarith
  -- Expand using toComplex to connect with the bilinear expansion
  let frC := toComplex fRe
  let fiC := toComplex fIm
  have hf : f = frC + Complex.I • fiC := by
    ext x
    simpa [frC, fiC, toComplex_apply, smul_eq_mul, complex_testfunction_decompose]
      using complex_testfunction_decompose_recompose f x
  -- Expand the bilinear form using bilinearity
  have h_expand : freeCovarianceℂ_bilinear m f f =
      freeCovarianceℂ_bilinear m frC frC + Complex.I * freeCovarianceℂ_bilinear m frC fiC +
      Complex.I * freeCovarianceℂ_bilinear m fiC frC - freeCovarianceℂ_bilinear m fiC fiC := by
    calc freeCovarianceℂ_bilinear m f f
      _ = freeCovarianceℂ_bilinear m (frC + Complex.I • fiC) (frC + Complex.I • fiC) := by rw [hf]
      _ = freeCovarianceℂ_bilinear m frC (frC + Complex.I • fiC) +
          freeCovarianceℂ_bilinear m (Complex.I • fiC) (frC + Complex.I • fiC) := by
        rw [freeCovarianceℂ_bilinear_add_left]
      _ = freeCovarianceℂ_bilinear m frC frC + freeCovarianceℂ_bilinear m frC (Complex.I • fiC) +
          (freeCovarianceℂ_bilinear m (Complex.I • fiC) frC +
           freeCovarianceℂ_bilinear m (Complex.I • fiC) (Complex.I • fiC)) := by
        rw [freeCovarianceℂ_bilinear_add_right, freeCovarianceℂ_bilinear_add_right]
      _ = freeCovarianceℂ_bilinear m frC frC + Complex.I * freeCovarianceℂ_bilinear m frC fiC +
          Complex.I * freeCovarianceℂ_bilinear m fiC frC - freeCovarianceℂ_bilinear m fiC fiC := by
        rw [freeCovarianceℂ_bilinear_smul_right, freeCovarianceℂ_bilinear_smul_left,
            freeCovarianceℂ_bilinear_smul_left, freeCovarianceℂ_bilinear_smul_right]
        -- Now we have I * (I * ...) which equals -(...) by I^2 = -1
        rw [show Complex.I * (Complex.I * freeCovarianceℂ_bilinear m fiC fiC) =
                 -(freeCovarianceℂ_bilinear m fiC fiC) by
                 rw [← mul_assoc, Complex.I_mul_I]; ring]
        ring
  -- Take real part: Re C(f,f) = Re C(frC,frC) - Re C(fiC,fiC)
  -- The cross terms with I have zero real part, so they vanish
  have h_re : (freeCovarianceℂ_bilinear m f f).re =
              (freeCovarianceℂ_bilinear m frC frC).re - (freeCovarianceℂ_bilinear m fiC fiC).re := by
    rw [h_expand]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    -- For real test functions frC and fiC, the bilinear form produces real values
    -- so the imaginary parts are zero
    have h_im_zero : (freeCovarianceℂ_bilinear m frC fiC).im = 0 := by
      -- Use agreement with the real covariance on real test functions
      have h := QFT.freeCovarianceℂ_bilinear_agrees_on_reals m fRe fIm
      -- Take imaginary parts; RHS is ofReal, hence zero imaginary part
      simpa [frC, fiC, Complex.ofReal_im] using congrArg Complex.im h
    have h_im_zero' : (freeCovarianceℂ_bilinear m fiC frC).im = 0 := by
      -- Use symmetry
      have : freeCovarianceℂ_bilinear m fiC frC = freeCovarianceℂ_bilinear m frC fiC :=
        freeCovarianceℂ_bilinear_symm m fiC frC
      rw [this, h_im_zero]
    simp [h_im_zero, h_im_zero']
  -- Therefore: -Re C(f,f) = -Re C(frC,frC) + Re C(fiC,fiC)
  rw [h_re]
  -- Since Re C(frC,frC) ≥ 0 by positivity, we have the bound
  have h_pos : 0 ≤ (freeCovarianceℂ_bilinear m frC frC).re := by
    -- For real test functions frC = toComplex fRe, the complex conjugate is the identity
    -- so freeCovarianceℂ_bilinear agrees with freeCovarianceℂ
    have heq : freeCovarianceℂ_bilinear m frC frC = freeCovarianceℂ m frC frC := by
      unfold freeCovarianceℂ_bilinear freeCovarianceℂ
      congr 1
      ext x
      congr 1
      ext y
      -- For real-valued functions, conjugation is identity
      have : starRingEnd ℂ (frC y) = frC y := by
        simp [frC, toComplex_apply]
      rw [this]
    rw [heq]
    exact freeCovarianceℂ_positive m frC
  linarith

/-
The covariance of the imaginary part is bounded by (1/m²) times the L² norm squared.
This uses the momentum space representation and the bound 1/(‖k‖² + m²) ≤ 1/m²,
plus Plancherel and the pointwise bound |Im f| ≤ |f|.
-/
/-- The GFF generating functional satisfies the exponential bound
    |Z[f]| ≤ exp((1/2m²)||f||²_{L²}). This combines the norm equality,
    the bound by imaginary part, and the L² bound to give the final OS1 estimate. -/
lemma gff_generating_L2_bound (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] (f : TestFunctionℂ) :
  ‖GJGeneratingFunctionalℂ (gaussianFreeField_free m) f‖ ≤
    Real.exp ((1 / (2 * m^2)) * ∫ x, ‖f x‖^2 ∂volume) := by
  set fIm := (complex_testfunction_decompose f).2
  calc ‖GJGeneratingFunctionalℂ (gaussianFreeField_free m) f‖
    _ = Real.exp (-(1/2) * (freeCovarianceℂ_bilinear m f f).re) := gff_generating_norm_eq m f
    _ ≤ Real.exp ((1/2) * (freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm)).re) :=
        gff_generating_bound_by_imaginary m f
    _ ≤ Real.exp ((1/2) * ((1 / m^2) * ∫ x, ‖f x‖^2 ∂volume)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (OSforGFF.covariance_imaginary_L2_bound (m := m) f) (by norm_num)
    _ = Real.exp ((1 / (2 * m^2)) * ∫ x, ‖f x‖^2 ∂volume) := by ring_nf

/-! ## Two-Point Function Local Integrability

Using the axioms above, we establish local integrability of the Schwinger function.
-/

/-- The two-point Schwinger function is locally integrable.
    This follows from the polynomial decay bound |S_2(x)| ≤ C|x|^{-2}.
    In d=4 spacetime dimensions, |x|^{-2} is locally integrable since 2 < 4. -/
lemma gff_two_point_locally_integrable (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
  TwoPointIntegrable (gaussianFreeField_free m) := by
  unfold TwoPointIntegrable
  -- Obtain the decay bound
  obtain ⟨C, hC_pos, h_decay⟩ := schwinger_two_point_decay_bound m
  -- Apply real version of the decay axiom
  refine locallyIntegrable_of_rpow_decay_real (d := STDimension) (C := C) (α := 2)
    ?hd ?hC ?hα ?h_decay ?h_meas
  · -- hd: STDimension = 4 ≥ 3
    norm_num [STDimension]
  · -- hC: C > 0
    exact hC_pos
  · -- hα: 2 < STDimension (2 < 4)
    norm_num [STDimension]
  · -- h_decay: Decay bound holds: convert two-argument decay to single-argument
    intro x
    -- We have h_decay: ‖S(x-y)‖ ≤ C * ‖x-y‖^{-2}, and need |S(x)| ≤ C * ‖x‖^{-2}
    -- Setting y = 0 gives ‖S(x-0)‖ = ‖S(x)‖ ≤ C * ‖x-0‖^{-2} = C * ‖x‖^{-2}
    have := h_decay x 0
    simp only [Real.norm_eq_abs, sub_zero] at this
    exact this
  · -- h_meas: Measurability (follows from Schwartz theory)
    exact schwingerTwoPoint_measurable m

/-! ## OS1 Verification for the GFF

Using the exponential L²-bound for the generating functional and local
integrability of the two-point function, we verify OS1 as stated in
`OS_Axioms.lean` (with the p-th power appearing inside the exponential).
-/

open MeasureTheory

/-- The Gaussian free field satisfies OS1 regularity with `p = 2` and
    `c = 1/(2 m^2)`. This uses `gff_generating_L2_bound` and
    `gff_two_point_locally_integrable` established above.

    Note: Named `_revised` because the alternative OS0 proof in `GaussianFreeField.lean`
    uses the same module; both are valid, and `GFFmaster.lean` uses this one. -/
theorem gaussianFreeField_satisfies_OS1_revised (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
  OS1_Regularity (gaussianFreeField_free m) := by
  -- Build a package instance and invoke the package-parametric OS1 proof.
  classical
  let P : OSforGFF.GFF.PackageOS1 (m := m) :=
    { (OSforGFF.GFF.packageOS0Proved (m := m)) with
      twoPointIntegrable := by
        simpa using (gff_two_point_locally_integrable (m := m)) }
  -- `P.μ` is definitionally the proved free GFF measure.
  simpa [P, OSforGFF.GFF.packageOS0Proved, OSforGFF.GFF.packageProved, gaussianFreeField_free] using
    (OSforGFF.GFF.PackageOS1.os1 (m := m) (P := P))
