/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.GFF.PackageOS0
import OSforGFF.ComplexTestFunction

/-!
## Complex characteristic functional from OS0 + the real characteristic functional

This file packages the main OS0-based analytic-continuation argument behind the interface
`OSforGFF.GFF.PackageOS0`:

- `PackageOS0.os0` supplies holomorphicity in finite-dimensional complex directions;
- `PackageOS0.gff_real_characteristic` supplies the real Gaussian formula.

From these, we derive the complex characteristic-functional identity
`Z[J] = exp(-½ freeCovarianceℂ_bilinear(J,J))` without depending on any particular backend
construction of the measure.
-/

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

namespace PackageOS0

variable {m : ℝ} [Fact (0 < m)] (P : PackageOS0 (m := m))

/-! ### Real bilinear expansion of the free covariance form -/

/-- Bilinearity expansion of `freeCovarianceFormR`:
`Q(tf+sg, tf+sg) = t²Q(f,f) + 2ts Q(f,g) + s²Q(g,g)`. -/
lemma freeCovarianceFormR_bilinear_expand (f g : TestFunction) (t s : ℝ) :
    freeCovarianceFormR m (t • f + s • g) (t • f + s • g) =
      t ^ 2 * freeCovarianceFormR m f f + 2 * t * s * freeCovarianceFormR m f g +
      s ^ 2 * freeCovarianceFormR m g g := by
  calc
    freeCovarianceFormR m (t • f + s • g) (t • f + s • g)
        = freeCovarianceFormR m (t • f) (t • f + s • g) +
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
    _ = t ^ 2 * freeCovarianceFormR m f f + 2 * t * s * freeCovarianceFormR m f g +
          s ^ 2 * freeCovarianceFormR m g g := by
            have hsym : freeCovarianceFormR m g f = freeCovarianceFormR m f g :=
              freeCovarianceFormR_symm m g f
            rw [hsym]
            ring

/-- The Gaussian CF formula for two real test functions (real parameters). -/
lemma gff_cf_two_testfunctions (f g : TestFunction) (t s : ℝ) :
    GJGeneratingFunctional P.μ (t • f + s • g) =
      Complex.exp (-(1 / 2 : ℂ) * (t ^ 2 * freeCovarianceFormR m f f +
        2 * t * s * freeCovarianceFormR m f g + s ^ 2 * freeCovarianceFormR m g g)) := by
  have h := P.gff_real_characteristic (t • f + s • g)
  rw [freeCovarianceFormR_bilinear_expand (m := m) (f := f) (g := g) (t := t) (s := s)] at h
  convert h using 2
  push_cast
  ring

/-! ### OS0 ⇒ analytic slices -/

omit [Fact (0 < m)] in
/-- OS0 specialized to two test functions gives differentiability of
`z ↦ Z[z₀•f + z₁•g]` as a map `ℂ² → ℂ`. -/
lemma gff_two_param_differentiable (f g : TestFunction) :
    Differentiable ℂ (fun z : Fin 2 → ℂ =>
      GJGeneratingFunctionalℂ P.μ (z 0 • toComplex f + z 1 • toComplex g)) := by
  have h := P.os0 2 ![toComplex f, toComplex g]
  convert h using 2
  congr 1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

omit [Fact (0 < m)] in
/-- Fixing one coordinate, the slice is analytic in the other. -/
lemma gff_slice_analytic_z0 (f g : TestFunction) (t : ℂ) :
    AnalyticOnNhd ℂ (fun z₀ : ℂ =>
      GJGeneratingFunctionalℂ P.μ (z₀ • toComplex f + t • toComplex g))
      Set.univ := by
  have h2param :
      Differentiable ℂ (fun z : Fin 2 → ℂ =>
        GJGeneratingFunctionalℂ P.μ (z 0 • toComplex f + z 1 • toComplex g)) :=
    gff_two_param_differentiable (m := m) P f g
  let e : ℂ → (Fin 2 → ℂ) := fun z₀ => (Pi.single 0 z₀) + (Pi.single 1 t)
  have he_diff : Differentiable ℂ e := by
    simpa [e] using
      (ContinuousLinearMap.differentiable (ContinuousLinearMap.single ℂ (fun _ : Fin 2 => ℂ) 0)).add
        (differentiable_const (c := Pi.single 1 t))
  have h_slice_diff :
      Differentiable ℂ (fun z₀ : ℂ =>
        GJGeneratingFunctionalℂ P.μ (z₀ • toComplex f + t • toComplex g)) := by
    have hcomp :
        Differentiable ℂ
          ((fun z : Fin 2 → ℂ =>
              GJGeneratingFunctionalℂ P.μ (z 0 • toComplex f + z 1 • toComplex g)) ∘ e) :=
      h2param.comp he_diff
    have hcomp' :
        Differentiable ℂ (fun z₀ : ℂ =>
          GJGeneratingFunctionalℂ P.μ
            ((e z₀) 0 • toComplex f + (e z₀) 1 • toComplex g)) := by
      simpa [Function.comp] using hcomp
    have h_eq :
        (fun z₀ : ℂ =>
          GJGeneratingFunctionalℂ P.μ
            ((e z₀) 0 • toComplex f + (e z₀) 1 • toComplex g)) =
          (fun z₀ : ℂ =>
            GJGeneratingFunctionalℂ P.μ (z₀ • toComplex f + t • toComplex g)) := by
      funext z₀
      have h0 : (e z₀) 0 = z₀ := by simp [e]
      have h1 : (e z₀) 1 = t := by simp [e]
      simp [h0, h1]
    simpa [h_eq] using hcomp'
  exact
    (analyticOnNhd_univ_iff_differentiable (f := fun z₀ : ℂ =>
      GJGeneratingFunctionalℂ P.μ (z₀ • toComplex f + t • toComplex g))).2 h_slice_diff

/-- Derived from `gff_slice_analytic_z0` by swapping `f`/`g`. -/
lemma gff_slice_analytic_z1 (f g : TestFunction) (z₀ : ℂ) :
    AnalyticOnNhd ℂ (fun z₁ : ℂ =>
      GJGeneratingFunctionalℂ P.μ (z₀ • toComplex f + z₁ • toComplex g))
      Set.univ := by
  have h := gff_slice_analytic_z0 (m := m) P g f z₀
  simp only [add_comm (z₀ • toComplex f)] at h ⊢
  convert h using 2

/-! ### Gaussian RHS analyticity (purely algebraic) -/

omit [Fact (0 < m)] in
/-- Slice of the Gaussian RHS is analytic (exp of polynomial). -/
lemma gaussian_rhs_slice_analytic_z0 (f g : TestFunction) (t : ℂ) :
    AnalyticOnNhd ℂ (fun z₀ : ℂ =>
      Complex.exp (-(1 / 2 : ℂ) * (z₀ ^ 2 * freeCovarianceFormR m f f +
        2 * z₀ * t * freeCovarianceFormR m f g + t ^ 2 * freeCovarianceFormR m g g)))
      Set.univ := by
  apply AnalyticOnNhd.cexp
  apply AnalyticOnNhd.mul analyticOnNhd_const
  apply AnalyticOnNhd.add
  apply AnalyticOnNhd.add
  · apply AnalyticOnNhd.mul _ (analyticOnNhd_const (v := (freeCovarianceFormR m f f : ℂ)))
    exact (analyticOnNhd_id (𝕜 := ℂ)).pow 2
  ·
    have h1 :
        AnalyticOnNhd ℂ (fun z₀ : ℂ => 2 * z₀ * t * freeCovarianceFormR m f g) Set.univ := by
      have :
          AnalyticOnNhd ℂ (fun z₀ : ℂ => (2 * t * freeCovarianceFormR m f g) * z₀) Set.univ :=
        AnalyticOnNhd.mul analyticOnNhd_const analyticOnNhd_id
      convert this using 2
      ring
    exact h1
  · exact analyticOnNhd_const

omit [Fact (0 < m)] in
/-- Slice of the Gaussian RHS is analytic in the second variable. -/
lemma gaussian_rhs_slice_analytic_z1 (f g : TestFunction) (z₀ : ℂ) :
    AnalyticOnNhd ℂ (fun z₁ : ℂ =>
      Complex.exp (-(1 / 2 : ℂ) * (z₀ ^ 2 * freeCovarianceFormR m f f +
        2 * z₀ * z₁ * freeCovarianceFormR m f g + z₁ ^ 2 * freeCovarianceFormR m g g)))
      Set.univ := by
  apply AnalyticOnNhd.cexp
  apply AnalyticOnNhd.mul analyticOnNhd_const
  apply AnalyticOnNhd.add
  apply AnalyticOnNhd.add
  · exact analyticOnNhd_const
  ·
    have h1 :
        AnalyticOnNhd ℂ (fun z₁ : ℂ => 2 * z₀ * z₁ * freeCovarianceFormR m f g) Set.univ := by
      have :
          AnalyticOnNhd ℂ (fun z₁ : ℂ => (2 * z₀ * freeCovarianceFormR m f g) * z₁) Set.univ :=
        AnalyticOnNhd.mul analyticOnNhd_const analyticOnNhd_id
      convert this using 2
      ring
    exact h1
  · apply AnalyticOnNhd.mul _ (analyticOnNhd_const (v := (freeCovarianceFormR m g g : ℂ)))
    exact (analyticOnNhd_id (𝕜 := ℂ)).pow 2

/-- Agreement on `ℝ²` between the complex GJ functional (restricted to real directions) and the
Gaussian RHS. -/
lemma gff_cf_agrees_on_reals_OS0 (f g : TestFunction) (t s : ℝ) :
    GJGeneratingFunctionalℂ P.μ ((t : ℂ) • toComplex f + (s : ℂ) • toComplex g) =
      Complex.exp (-(1 / 2 : ℂ) * ((t : ℂ) ^ 2 * freeCovarianceFormR m f f +
        2 * (t : ℂ) * (s : ℂ) * freeCovarianceFormR m f g + (s : ℂ) ^ 2 * freeCovarianceFormR m g g)) := by
  have h := gff_cf_two_testfunctions (m := m) P f g t s
  have h_eq_test :
      (t : ℂ) • toComplex f + (s : ℂ) • toComplex g = toComplex (t • f + s • g) := by
    ext x
    simp [toComplex_apply]
  rw [h_eq_test]
  -- Reduce to the real generating functional using `toComplex`, then apply the real CF formula.
  rw [GJGeneratingFunctionalℂ_toComplex (dμ_config := P.μ) (t • f + s • g)]
  simp [h]

/-! ### Main theorem -/

/-- Complex characteristic functional from OS0 + the real characteristic-functional identity. -/
theorem gff_complex_characteristic_OS0 :
    ∀ J : TestFunctionℂ,
      GJGeneratingFunctionalℂ P.μ J =
        Complex.exp (-(1 / 2 : ℂ) * freeCovarianceℂ_bilinear m J J) := by
  intro J
  let f := (complex_testfunction_decompose J).1
  let g := (complex_testfunction_decompose J).2
  have hJ : J = toComplex f + Complex.I • toComplex g := by
    ext x
    simpa [f, g, toComplex_apply, smul_eq_mul, complex_testfunction_decompose]
      using complex_testfunction_decompose_recompose J x
  let F : ℂ → ℂ → ℂ := fun z₀ z₁ =>
    GJGeneratingFunctionalℂ P.μ (z₀ • toComplex f + z₁ • toComplex g)
  let G : ℂ → ℂ → ℂ := fun z₀ z₁ =>
    Complex.exp (-(1 / 2 : ℂ) * (z₀ ^ 2 * freeCovarianceFormR m f f +
      2 * z₀ * z₁ * freeCovarianceFormR m f g + z₁ ^ 2 * freeCovarianceFormR m g g))

  have h_agree_real : ∀ t s : ℝ, F t s = G t s := by
    intro t s
    simp only [F, G]
    exact gff_cf_agrees_on_reals_OS0 (m := m) P f g t s

  have h_step1 : ∀ (s : ℝ) (z₀ : ℂ), F z₀ s = G z₀ s := by
    intro s z₀
    have hF_an : AnalyticOnNhd ℂ (fun z₀ => F z₀ s) Set.univ :=
      gff_slice_analytic_z0 (m := m) P f g s
    have hG_an : AnalyticOnNhd ℂ (fun z₀ => G z₀ s) Set.univ :=
      gaussian_rhs_slice_analytic_z0 (m := m) (f := f) (g := g) (t := s)
    have h_agree_slice : ∀ t : ℝ, F t s = G t s := fun t => h_agree_real t s
    have h_eq : (fun z₀ => F z₀ s) = (fun z₀ => G z₀ s) := by
      apply AnalyticOnNhd.eq_of_frequently_eq hF_an hG_an (z₀ := 0)
      simp only [Filter.Frequently]
      intro hU
      rw [Filter.Eventually, mem_nhdsWithin] at hU
      obtain ⟨V, hV_open, h0_in_V, hV_sub⟩ := hU
      obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0_in_V
      have h_half_pos : (0 : ℝ) < ε / 2 := half_pos hε_pos
      have h_mem_V : ((ε / 2 : ℝ) : ℂ) ∈ V := hε_ball (by
        simp only [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_real]
        rw [Real.norm_eq_abs, abs_of_pos h_half_pos]
        linarith)
      have h_ne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        linarith
      have h_in : ((ε / 2 : ℝ) : ℂ) ∈ V ∩ {(0 : ℂ)}ᶜ := ⟨h_mem_V, h_ne⟩
      exact hV_sub h_in (h_agree_slice (ε / 2))
    exact congrFun h_eq z₀

  have h_step2 : ∀ z₀ z₁ : ℂ, F z₀ z₁ = G z₀ z₁ := by
    intro z₀ z₁
    have hF_an : AnalyticOnNhd ℂ (fun z₁ => F z₀ z₁) Set.univ :=
      gff_slice_analytic_z1 (m := m) P f g z₀
    have hG_an : AnalyticOnNhd ℂ (fun z₁ => G z₀ z₁) Set.univ :=
      gaussian_rhs_slice_analytic_z1 (m := m) (f := f) (g := g) (z₀ := z₀)
    have h_agree_slice : ∀ s : ℝ, F z₀ s = G z₀ s := fun s => h_step1 s z₀
    have h_eq : (fun z₁ => F z₀ z₁) = (fun z₁ => G z₀ z₁) := by
      apply AnalyticOnNhd.eq_of_frequently_eq hF_an hG_an (z₀ := 0)
      simp only [Filter.Frequently]
      intro hU
      rw [Filter.Eventually, mem_nhdsWithin] at hU
      obtain ⟨V, hV_open, h0_in_V, hV_sub⟩ := hU
      obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0_in_V
      have h_half_pos : (0 : ℝ) < ε / 2 := half_pos hε_pos
      have h_mem_V : ((ε / 2 : ℝ) : ℂ) ∈ V := hε_ball (by
        simp only [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_real]
        rw [Real.norm_eq_abs, abs_of_pos h_half_pos]
        linarith)
      have h_ne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        linarith
      have h_in : ((ε / 2 : ℝ) : ℂ) ∈ V ∩ {(0 : ℂ)}ᶜ := ⟨h_mem_V, h_ne⟩
      exact hV_sub h_in (h_agree_slice (ε / 2))
    exact congrFun h_eq z₁

  have h_eval : F 1 Complex.I = G 1 Complex.I := h_step2 1 Complex.I

  have h_LHS : GJGeneratingFunctionalℂ P.μ J = F 1 Complex.I := by
    simp only [F, hJ]
    congr 1
    simp [one_smul]

  have h_RHS : Complex.exp (-(1 / 2 : ℂ) * freeCovarianceℂ_bilinear m J J) = G 1 Complex.I := by
    simp only [G]
    congr 1
    have h_Qc : freeCovarianceℂ_bilinear m J J =
        freeCovarianceFormR m f f - freeCovarianceFormR m g g +
          2 * Complex.I * freeCovarianceFormR m f g := by
      rw [hJ]
      rw [freeCovarianceℂ_bilinear_add_left, freeCovarianceℂ_bilinear_add_right,
        freeCovarianceℂ_bilinear_add_right]
      simp only [freeCovarianceℂ_bilinear_smul_left, freeCovarianceℂ_bilinear_smul_right]
      have h_ff := freeCovarianceℂ_bilinear_agrees_on_reals (m := m) f f
      have h_fg := freeCovarianceℂ_bilinear_agrees_on_reals (m := m) f g
      have h_gf := freeCovarianceℂ_bilinear_agrees_on_reals (m := m) g f
      have h_gg := freeCovarianceℂ_bilinear_agrees_on_reals (m := m) g g
      rw [h_ff, h_fg, h_gf, h_gg]
      have h_sym : freeCovarianceFormR m g f = freeCovarianceFormR m f g :=
        freeCovarianceFormR_symm m g f
      rw [h_sym]
      have hII : Complex.I * (Complex.I * (freeCovarianceFormR m g g : ℂ)) =
          -(freeCovarianceFormR m g g : ℂ) := by
        rw [← mul_assoc, Complex.I_mul_I]
        ring
      rw [hII]
      ring
    rw [h_Qc]
    simp only [one_pow, Complex.I_sq, one_mul]
    ring

  rw [h_LHS, h_eval, ← h_RHS]

end PackageOS0

end
end GFF
end OSforGFF
