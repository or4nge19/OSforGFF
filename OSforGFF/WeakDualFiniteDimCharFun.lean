import OSforGFF.WeakDualCylindrical
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-!
# Finite-dimensional characteristic-functional bridge on `WeakDual`

This file packages the finite-dimensional “cylinder characteristic function” identities used in
Minlos/Bochner arguments.
-/

namespace OSforGFF

open scoped BigOperators RealInnerProductSpace
open MeasureTheory Complex

noncomputable section

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

local instance : MeasurableSpace (WeakDual ℝ E) :=
  weakDualCylMeasurableSpace (𝕜 := ℝ) (E := E)

/-- Finite-dimensional oscillatory integral built from evaluations `ω (fs i)`. -/
def weakDualJointCharFun (μ : Measure (WeakDual ℝ E)) (n : ℕ) (fs : Fin n → E) (t : Fin n → ℝ) : ℂ :=
  MeasureTheory.integral μ fun ω =>
    Complex.exp (((Finset.univ.sum (fun i : Fin n => (t i) * (ω (fs i))) : ℝ) : ℂ) * I)

/-- **Core bridge:** the joint characteristic function depends only on `∑ i, t i • fs i`. -/
theorem weakDualJointCharFun_eq_eval (μ : Measure (WeakDual ℝ E)) (n : ℕ) (fs : Fin n → E)
    (t : Fin n → ℝ) :
    weakDualJointCharFun (E := E) μ n fs t =
      MeasureTheory.integral μ (fun ω =>
        Complex.exp (((ω (∑ i : Fin n, (t i) • fs i) : ℝ) : ℂ) * I)) := by
  classical
  have hω (ω : WeakDual ℝ E) :
      (ω (∑ i : Fin n, (t i) • fs i) : ℝ) =
        Finset.univ.sum (fun i : Fin n => (t i) * (ω (fs i))) := by
    simp
  simp [weakDualJointCharFun, hω]

/-- The joint characteristic function equals the corresponding oscillatory integral over the
finite-dimensional pushforward `μ.map (weakDualProj fs)`. -/
theorem weakDualJointCharFun_eq_integral_map (μ : Measure (WeakDual ℝ E)) (n : ℕ) (fs : Fin n → E)
    (t : Fin n → ℝ) :
    weakDualJointCharFun (E := E) μ n fs t =
      MeasureTheory.integral (μ.map (weakDualProj (𝕜 := ℝ) (E := E) fs)) (fun x : (Fin n → ℝ) =>
        Complex.exp (((Finset.univ.sum (fun i : Fin n => (t i) * (x i)) : ℝ) : ℂ) * I)) := by
  classical
  have hproj :
      AEMeasurable (weakDualProj (𝕜 := ℝ) (E := E) fs) μ :=
    (measurable_weakDualProj (𝕜 := ℝ) (E := E) fs).aemeasurable

  have hsum_meas :
      Measurable fun x : (Fin n → ℝ) =>
        (Finset.univ.sum fun i : Fin n => (t i) * (x i)) := by
    have hterm :
        ∀ i ∈ (Finset.univ : Finset (Fin n)),
          Measurable fun x : (Fin n → ℝ) => (t i) * (x i) := by
      intro i hi
      simpa using (measurable_const.mul (measurable_pi_apply i))
    simpa using
      (Finset.measurable_fun_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i (x : Fin n → ℝ) => (t i) * (x i)) hterm)

  have hintegrand_meas :
      Measurable fun x : (Fin n → ℝ) =>
        Complex.exp (((((Finset.univ.sum (fun i : Fin n => (t i) * (x i))) : ℝ) : ℂ) * I)) := by
    have hsumC' :
        Measurable fun x : (Fin n → ℝ) =>
          (((Finset.univ.sum (fun i : Fin n => (t i) * (x i)) : ℝ) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp hsum_meas
    have harg :
        Measurable fun x : (Fin n → ℝ) =>
          (((((Finset.univ.sum (fun i : Fin n => (t i) * (x i)) : ℝ) : ℝ) : ℂ) * I)) :=
      hsumC'.mul measurable_const
    simpa using (Complex.continuous_exp.measurable.comp harg)

  have hintegrand_strong :
      AEStronglyMeasurable
        (fun x : (Fin n → ℝ) =>
          Complex.exp (((((Finset.univ.sum (fun i : Fin n => (t i) * (x i))) : ℝ) : ℂ) * I)))
        (μ.map (weakDualProj (𝕜 := ℝ) (E := E) fs)) :=
    hintegrand_meas.aestronglyMeasurable

  symm
  rw [integral_map hproj hintegrand_strong]
  simp [weakDualJointCharFun, PhysLean.Mathematics.Distribution.weakDualProj]

end

end

end OSforGFF

