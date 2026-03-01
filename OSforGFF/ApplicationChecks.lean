/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import OSforGFF.Basic
import OSforGFF.WeakDualCylindrical
import OSforGFF.Spacetime.TimeDirection

/-!
# Consolidation application checks

This module contains small `example`s that ensure `OSforGFF` is using the consolidated core APIs
from `PhysLean` (cylindrical σ-algebra on `WeakDual`, coordinate-free time-direction operations,
and vector-valued Schwartz actions).
-/

namespace OSforGFF

section WeakDualMeasurable

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]

example :
    OSforGFF.weakDualCylMeasurableSpace (𝕜 := ℝ) (E := E) =
      PhysLean.Mathematics.Distribution.weakDualCylMeasurableSpace (𝕜 := ℝ) (E := E) := rfl

end WeakDualMeasurable

section TimeDirectionVectorValued

open scoped RealInnerProductSpace

-- Vector-valued Schwartz operations used for Yang–Mills-style test functions.
example :
    let τ : SpaceTime.TimeDirection ℝ := ⟨(1 : ℝ), by simp⟩
    ∀ (t : ℝ) (f : SchwartzMap ℝ (Fin 2 → ℂ)) (x : ℝ),
      τ.translateAlongTestFunction (𝕜 := ℂ) (F := (Fin 2 → ℂ)) t f x = f (x - t • τ.vec) := by
  intro τ t f x
  simpa using (SpaceTime.TimeDirection.translateAlongTestFunction_apply
    (τ := τ) (𝕜 := ℂ) (F := (Fin 2 → ℂ)) t f x)

example :
    let τ : SpaceTime.TimeDirection ℝ := ⟨(1 : ℝ), by simp⟩
    let ops : SpaceTime.TimeDirectionOps ℝ τ :=
      { reflect := LinearIsometryEquiv.neg (R := ℝ) (E := ℝ)
        reflect_timeCoord := by
          intro x
          simpa using (τ.timeCoord.map_neg x)
        reflect_involutive := by
          intro x
          simp
        reflect_fix_hyperplane := by
          intro x hx
          have hcoord : τ.timeCoord x = x := by
            simpa [τ] using (τ.timeCoord_smul_vec x)
          have hx0 : x = 0 := by
            simpa [hcoord] using hx
          simp [hx0] }
    ∀ (f : SchwartzMap ℝ (Fin 2 → ℂ)) (x : ℝ),
      ops.reflectTestFunction (𝕜 := ℂ) (F := (Fin 2 → ℂ)) f x = f (ops.reflect x) := by
  intro τ ops f x
  rfl

end TimeDirectionVectorValued

end OSforGFF

