/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import OSforGFF.GaussianMoments
import OSforGFF.GFF.ComplexCharacteristicProved
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
## Complex GFF Results (bridging + polarization)

This file assembles the main “GFF is Gaussian” consequences for the proved free GFF measure.

The complex characteristic functional identity is provided by
`OSforGFF/GFF/ComplexCharacteristicProved.lean`, so this file focuses on:
- extracting the two-point function from second moments, and
- packaging the resulting Gaussianity statement.

### Main Results:
1. `gff_two_point_equals_covarianceℂ_free`: S₂(f,g) = freeCovarianceℂ(f,g)
2. `gff_complex_generating`: Z[J] = exp(-½ S₂(J,J))
3. `isGaussianGJ_gaussianFreeField_free`: The free GFF is Gaussian

### Proof Strategy:
From `gff_real_characteristic`: Z[tf+sg] = exp(-½ Q(tf+sg, tf+sg))
Expanding: = exp(-½(t²Q(f,f) + 2ts Q(f,g) + s²Q(g,g)))
Using the (proved) second-moment identity for the pairing and polarization,
we recover the mixed second moment and identify \(S₂(f,g)\) with the covariance form.
-/

open MeasureTheory Complex QFT

noncomputable section

/-! ## Main Results -/

namespace GFFIsGaussian

variable (m : ℝ) [Fact (0 < m)]
variable [OSforGFF.NuclearSpaceStd TestFunction]

/-- For the Gaussian Free Field measure, the product of two complex pairings with test functions
    is integrable. Uses the direct 2-point theorem from GaussianMoments. -/
lemma gaussian_pairing_product_integrable_free_core
    (φ ψ : TestFunctionℂ) :
    Integrable (fun ω => distributionPairingℂ_real ω φ * distributionPairingℂ_real ω ψ)
      (gaussianFreeField_free m).toMeasure :=
  gaussian_pairing_product_integrable_free_2point m φ ψ

/-! ## Core Theorems

The proofs use OS0's derivative interchange machinery:
1. `gff_real_characteristic` gives Z[f] = exp(-½ Q(f,f)) for real f
2. `gaussianFreeField_satisfies_OS0` gives analyticity of Z
3. `hasFDerivAt_integral_of_dominated_of_fderiv_le` (used in OS0) gives derivative interchange
4. Computing ∂²Z/∂t∂s|₀ two ways (Gaussian formula vs integral) gives S₂ = Q
-/

omit [OSforGFF.NuclearSpaceStd TestFunction] in
/-- Bilinearity expansion of Q(tf+sg, tf+sg).
    Q(tf+sg, tf+sg) = t²Q(f,f) + 2ts Q(f,g) + s²Q(g,g) -/
lemma freeCovarianceFormR_bilinear_expand (f g : TestFunction) (t s : ℝ) :
    freeCovarianceFormR m (t • f + s • g) (t • f + s • g) =
      t^2 * freeCovarianceFormR m f f + 2 * t * s * freeCovarianceFormR m f g +
      s^2 * freeCovarianceFormR m g g := by
  -- Expand using add_left/right and smul_left/right
  calc freeCovarianceFormR m (t • f + s • g) (t • f + s • g)
    _ = freeCovarianceFormR m (t • f) (t • f + s • g) +
        freeCovarianceFormR m (s • g) (t • f + s • g) := by
          rw [freeCovarianceFormR_add_left]
    _ = freeCovarianceFormR m (t • f) (t • f) + freeCovarianceFormR m (t • f) (s • g) +
        (freeCovarianceFormR m (s • g) (t • f) + freeCovarianceFormR m (s • g) (s • g)) := by
          rw [freeCovarianceFormR_add_right, freeCovarianceFormR_add_right]
    _ = t * freeCovarianceFormR m f (t • f) + t * freeCovarianceFormR m f (s • g) +
        (s * freeCovarianceFormR m g (t • f) + s * freeCovarianceFormR m g (s • g)) := by
          simp only [freeCovarianceFormR_smul_left]
    _ = t * (t * freeCovarianceFormR m f f) + t * (s * freeCovarianceFormR m f g) +
        (s * (t * freeCovarianceFormR m g f) + s * (s * freeCovarianceFormR m g g)) := by
          simp only [freeCovarianceFormR_smul_right]
    _ = t^2 * freeCovarianceFormR m f f + 2 * t * s * freeCovarianceFormR m f g +
        s^2 * freeCovarianceFormR m g g := by
          -- Use symmetry: Q(g,f) = Q(f,g)
          have hsym : freeCovarianceFormR m g f = freeCovarianceFormR m f g :=
            freeCovarianceFormR_symm m g f
          rw [hsym]; ring

/-- The Gaussian CF formula for two test functions. -/
lemma gff_cf_two_testfunctions (f g : TestFunction) (t s : ℝ) :
    GJGeneratingFunctional (gaussianFreeField_free m) (t • f + s • g) =
      Complex.exp (-(1/2 : ℂ) * (t^2 * freeCovarianceFormR m f f +
        2 * t * s * freeCovarianceFormR m f g + s^2 * freeCovarianceFormR m g g)) := by
  have h := gff_real_characteristic m (t • f + s • g)
  rw [freeCovarianceFormR_bilinear_expand] at h
  convert h using 2
  push_cast; ring

/-- Complex generating functional for the free GFF.

This is now proved by specializing the backend-agnostic OS0 continuation theorem to the proved
free GFF construction. -/
theorem gff_complex_characteristic_OS0 :
    ∀ J : TestFunctionℂ,
      GJGeneratingFunctionalℂ (gaussianFreeField_free m) J =
        Complex.exp (-(1/2 : ℂ) * freeCovarianceℂ_bilinear m J J) := by
  intro J
  simpa using (OSforGFF.GFF.gff_complex_characteristic_OS0_proved (m := m) J)

/-! ## Polarization-Based Proof

The key insight is to use the **polarization identity** instead of derivative calculus.

For a centered Gaussian:
- E[⟨ω,f⟩²] = Q(f,f) (this is `gff_second_moment_eq_covariance` from GFFbridge)

By polarization:
- E[XY] = ¼(E[(X+Y)²] - E[(X-Y)²])
- With X = ⟨ω,f⟩, Y = ⟨ω,g⟩:
  E[⟨ω,f⟩⟨ω,g⟩] = ¼(Q(f+g,f+g) - Q(f-g,f-g)) = Q(f,g)

This avoids all derivative calculus! -/

/-- For real test functions, the second moment equals the covariance.
    S₂(f,g) = Q(f,g) = freeCovarianceFormR(f,g)

    Proof via polarization identity:
    E[XY] = ¼(E[(X+Y)²] - E[(X-Y)²])
         = ¼(Q(f+g,f+g) - Q(f-g,f-g))
         = Q(f,g) by bilinearity -/
theorem schwinger_eq_covariance_real (f g : TestFunction) :
    ∫ ω, (ω f) * (ω g) ∂(gaussianFreeField_free m).toMeasure =
      freeCovarianceFormR m f g := by
  -- Use polarization identity: XY = ¼((X+Y)² - (X-Y)²)
  have h_polar : ∀ ω : FieldConfiguration,
      (ω f) * (ω g) = (1/4 : ℝ) * ((ω (f + g))^2 - (ω (f - g))^2) := by
    intro ω
    -- Linearity of pairing
    simp only [map_add, map_sub]
    ring
  simp_rw [h_polar]
  rw [MeasureTheory.integral_const_mul]
  -- Use gff_second_moment_eq_covariance for each term
  have h_sq_fg : ∫ ω, (ω (f + g))^2 ∂(gaussianFreeField_free m).toMeasure =
      freeCovarianceFormR m (f + g) (f + g) := by
    have := gff_second_moment_eq_covariance m (f + g)
    simp only [distributionPairingCLM_apply, distributionPairing] at this
    exact this
  have h_sq_f_g : ∫ ω, (ω (f - g))^2 ∂(gaussianFreeField_free m).toMeasure =
      freeCovarianceFormR m (f - g) (f - g) := by
    have := gff_second_moment_eq_covariance m (f - g)
    simp only [distributionPairingCLM_apply, distributionPairing] at this
    exact this
  rw [integral_sub, h_sq_fg, h_sq_f_g]
  -- Expand using bilinearity of Q
  -- Q(f+g,f+g) = Q(f,f) + 2Q(f,g) + Q(g,g)
  -- Q(f-g,f-g) = Q(f,f) - 2Q(f,g) + Q(g,g)
  -- Difference = 4Q(f,g)
  -- Use f - g = f + (-1) • g for subtraction
  have h_sub : f - g = f + (-1 : ℝ) • g := by simp [sub_eq_add_neg, neg_smul, one_smul]
  -- Expand Q(f+g, f+g)
  have h_expand_plus : freeCovarianceFormR m (f + g) (f + g) =
      freeCovarianceFormR m f f + 2 * freeCovarianceFormR m f g + freeCovarianceFormR m g g := by
    rw [freeCovarianceFormR_add_left, freeCovarianceFormR_add_right, freeCovarianceFormR_add_right]
    rw [freeCovarianceFormR_symm m g f]
    ring
  -- Expand Q(f-g, f-g)
  have h_expand_minus : freeCovarianceFormR m (f - g) (f - g) =
      freeCovarianceFormR m f f - 2 * freeCovarianceFormR m f g + freeCovarianceFormR m g g := by
    rw [h_sub]
    rw [freeCovarianceFormR_add_left, freeCovarianceFormR_add_right, freeCovarianceFormR_add_right]
    rw [freeCovarianceFormR_smul_left, freeCovarianceFormR_smul_right, freeCovarianceFormR_smul_left,
        freeCovarianceFormR_smul_right]
    rw [freeCovarianceFormR_symm m g f]
    ring
  rw [h_expand_plus, h_expand_minus]
  ring
  -- Integrability for subtraction
  · exact gff_pairing_square_integrable m (f + g)
  · exact gff_pairing_square_integrable m (f - g)

/-- For real test functions embedded into complex, the Schwinger 2-point function
    equals the complex covariance. -/
lemma schwinger_eq_covarianceℂ_on_reals (f g : TestFunction) :
    SchwingerFunctionℂ₂ (gaussianFreeField_free m) (toComplex f) (toComplex g) =
      freeCovarianceℂ_bilinear m (toComplex f) (toComplex g) := by
  -- Use distributionPairingℂ_real_toComplex to reduce to real pairings
  simp only [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    distributionPairingℂ_real_toComplex]
  -- Now we have: ∫ ω, ↑(ω f) * ↑(ω g) dμ = freeCovarianceℂ_bilinear m (toComplex f) (toComplex g)
  -- Step 1: Rewrite ↑a * ↑b = ↑(a * b) pointwise using ofReal_mul
  simp_rw [← Complex.ofReal_mul]
  -- Step 2: Integrability of the product
  have h_int : Integrable (fun ω => distributionPairing ω f * distributionPairing ω g)
      (gaussianFreeField_free m).toMeasure := by
    -- Use Hölder: L² × L² → L¹
    have hf : MemLp (fun ω => distributionPairing ω f) 2 (gaussianFreeField_free m).toMeasure :=
      gaussianFreeField_pairing_memLp m f 2 (by simp)
    have hg : MemLp (fun ω => distributionPairing ω g) 2 (gaussianFreeField_free m).toMeasure :=
      gaussianFreeField_pairing_memLp m g 2 (by simp)
    exact hf.integrable_mul hg
  -- Step 3–4: Pull the `ℝ → ℂ` cast outside the integral, then use the real identity and
  -- `freeCovarianceℂ_bilinear_agrees_on_reals`.
  calc
    ∫ (ω : FieldConfiguration), ↑(distributionPairing ω f * distributionPairing ω g)
        ∂↑(gaussianFreeField_free m) =
        (↑(∫ (ω : FieldConfiguration), distributionPairing ω f * distributionPairing ω g
            ∂(gaussianFreeField_free m).toMeasure) : ℂ) := by
          -- `∫ (f : ℝ) = (∫ f : ℝ)` coerced to `ℂ`.
          simpa using (integral_ofReal (𝕜 := ℂ)
            (μ := (gaussianFreeField_free m).toMeasure)
            (f := fun ω => distributionPairing ω f * distributionPairing ω g))
    _ = (freeCovarianceFormR m f g : ℂ) := by
          simpa using congrArg (↑· : ℝ → ℂ) (schwinger_eq_covariance_real m f g)
    _ = freeCovarianceℂ_bilinear m (toComplex f) (toComplex g) := by
          simpa using (freeCovarianceℂ_bilinear_agrees_on_reals m f g).symm

end GFFIsGaussian

/-! ## Main Theorems (at root level for compatibility) -/

/-- For complex test functions, the Schwinger 2-point function equals the complex covariance.

    S₂(μ, f, g) = freeCovarianceℂ_bilinear m f g

    This extends schwinger_eq_covariance_real to complex test functions by bilinearity:
    both S₂ and freeCovarianceℂ_bilinear are bilinear, and they agree on real inputs.

    For any complex f = fRe + I•fIm, g = gRe + I•gIm, we expand by bilinearity. -/
theorem gff_two_point_equals_covarianceℂ_free (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] (f g : TestFunctionℂ) :
    SchwingerFunctionℂ₂ (gaussianFreeField_free m) f g = freeCovarianceℂ_bilinear m f g := by
  -- Decompose complex test functions into real and imaginary parts
  let fRe := (complex_testfunction_decompose f).1
  let fIm := (complex_testfunction_decompose f).2
  let gRe := (complex_testfunction_decompose g).1
  let gIm := (complex_testfunction_decompose g).2
  let frC := toComplex fRe
  let fiC := toComplex fIm
  let grC := toComplex gRe
  let giC := toComplex gIm
  -- Prove the decompositions: f = frC + I • fiC, g = grC + I • giC
  have hf : f = frC + Complex.I • fiC := by
    ext x
    simpa [frC, fiC, toComplex_apply, smul_eq_mul, complex_testfunction_decompose]
      using complex_testfunction_decompose_recompose f x
  have hg : g = grC + Complex.I • giC := by
    ext x
    simpa [grC, giC, toComplex_apply, smul_eq_mul, complex_testfunction_decompose]
      using complex_testfunction_decompose_recompose g x
  rw [hf, hg]
  -- Extract bilinearity properties from CovarianceBilinear
  -- CovarianceBilinear gives: ∀ c φ₁ φ₂ ψ,
  --   .1: S₂(c • φ₁, ψ) = c * S₂(φ₁, ψ)
  --   .2.1: S₂(φ₁ + φ₂, ψ) = S₂(φ₁, ψ) + S₂(φ₂, ψ)
  --   .2.2.1: S₂(φ₁, c • ψ) = c * S₂(φ₁, ψ)
  --   .2.2.2: S₂(φ₁, ψ + φ₂) = S₂(φ₁, ψ) + S₂(φ₁, φ₂)
  have h_bilin := covariance_bilinear_from_general m
  have S2_smul_left : ∀ (c : ℂ) a b, SchwingerFunctionℂ₂ (gaussianFreeField_free m) (c • a) b =
      c * SchwingerFunctionℂ₂ (gaussianFreeField_free m) a b :=
    fun c a b => (h_bilin c a 0 b).1
  have S2_add_left : ∀ a b c, SchwingerFunctionℂ₂ (gaussianFreeField_free m) (a + b) c =
      SchwingerFunctionℂ₂ (gaussianFreeField_free m) a c + SchwingerFunctionℂ₂ (gaussianFreeField_free m) b c :=
    fun a b c => (h_bilin 1 a b c).2.1
  have S2_smul_right : ∀ (c : ℂ) a b, SchwingerFunctionℂ₂ (gaussianFreeField_free m) a (c • b) =
      c * SchwingerFunctionℂ₂ (gaussianFreeField_free m) a b :=
    fun c a b => (h_bilin c a 0 b).2.2.1
  have S2_add_right : ∀ a b c, SchwingerFunctionℂ₂ (gaussianFreeField_free m) a (b + c) =
      SchwingerFunctionℂ₂ (gaussianFreeField_free m) a b + SchwingerFunctionℂ₂ (gaussianFreeField_free m) a c :=
    fun a b c => (h_bilin 1 a c b).2.2.2
  -- Expand LHS: S₂(frC + I•fiC, grC + I•giC)
  rw [S2_add_left, S2_add_right, S2_add_right, S2_smul_left, S2_smul_left, S2_smul_right,
      S2_smul_right]
  -- Expand RHS: freeCovarianceℂ_bilinear(frC + I•fiC, grC + I•giC)
  simp only [freeCovarianceℂ_bilinear_add_left, freeCovarianceℂ_bilinear_add_right,
    freeCovarianceℂ_bilinear_smul_left, freeCovarianceℂ_bilinear_smul_right]
  -- Both sides have 4 terms. Rewrite S₂(toComplex ?, toComplex ?) = C(toComplex ?, toComplex ?)
  -- frC = toComplex fRe, fiC = toComplex fIm, grC = toComplex gRe, giC = toComplex gIm
  rw [GFFIsGaussian.schwinger_eq_covarianceℂ_on_reals m fRe gRe,
      GFFIsGaussian.schwinger_eq_covarianceℂ_on_reals m fRe gIm,
      GFFIsGaussian.schwinger_eq_covarianceℂ_on_reals m fIm gRe,
      GFFIsGaussian.schwinger_eq_covarianceℂ_on_reals m fIm gIm]
  -- Now both sides are equal up to commutativity of addition
  ring

/-- Complex generating functional for the free GFF: Z[J] = exp(-½ S₂(J,J))

    This follows from gff_real_characteristic (for real J) extended to complex J
    via analyticity (gaussianFreeField_satisfies_OS0). Both sides are analytic in J
    and agree on real J, hence they are equal everywhere. -/
theorem gff_complex_generating (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    ∀ J : TestFunctionℂ,
      GJGeneratingFunctionalℂ (gaussianFreeField_free m) J =
        Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ (gaussianFreeField_free m) J J) := by
  intro J
  -- Use gff_two_point_equals_covarianceℂ_free: S₂ = freeCovarianceℂ_bilinear
  rw [gff_two_point_equals_covarianceℂ_free (m := m) (f := J) (g := J)]
  -- Now goal is: Z[J] = exp(-½ freeCovarianceℂ_bilinear m J J)
  -- Use gff_complex_characteristic_OS0 (via OS0 + identity theorem, no MinlosAnalytic dependency)
  exact GFFIsGaussian.gff_complex_characteristic_OS0 m J

/-- The Gaussian Free Field constructed via Minlos is Gaussian.

    This combines:
    1. Centering: E[⟨ω,φ⟩] = 0 (from gaussianFreeField_free_centered)
    2. Gaussian CF: Z[J] = exp(-½ S₂(J,J)) (from gff_complex_generating) -/
theorem isGaussianGJ_gaussianFreeField_free (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    isGaussianGJ (gaussianFreeField_free m) := by
  constructor
  · exact gaussianFreeField_free_centered m
  · intro J; simpa using (gff_complex_generating (m := m) J)
