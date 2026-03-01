/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import PhysLean.SpaceAndTime.Space.Basic
/-!
# Euclidean time-direction operations

## i. Overview

This file provides a coordinate-free interface for Osterwalder–Schrader “time” operations
in an ambient real inner product space:

- a distinguished unit vector (the time direction),
- the associated time-coordinate continuous linear functional,
- scalar-time translations along the chosen direction,
- a reflection operator compatible with the time coordinate,
- induced actions on Schwartz test functions.

## ii. Main statements

- `TimeDirection` : a unit vector `vec` in a real inner product space.
- `TimeDirection.timeCoord` : the continuous linear time-coordinate functional `x ↦ ⟪vec, x⟫`.
- `TimeDirection.translateAlong` : translations `x ↦ x + t • vec` and basic lemmas.
- `TimeDirectionOps` : reflection data compatible with `timeCoord`.
- `TimeDirection.translateAlongTestFunction` : translation as a continuous linear map on Schwartz maps.
- `TimeDirectionOps.reflectTestFunction` : reflection as a continuous linear map on Schwartz maps.

## iii. Table of contents

- A. Time direction and time coordinate
- B. Translations along the time direction
- C. Reflection operations and half-spaces
- D. Induced actions on Schwartz test functions

## iv. References

- Osterwalder–Schrader axioms for Euclidean QFT.
-/

noncomputable section

namespace SpaceTime

open MeasureTheory

/-!
## A. Time direction and time coordinate
-/

/-- Choice of Euclidean time direction: a unit vector `vec`. -/
structure TimeDirection (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  vec : E
  norm_eq_one : ‖vec‖ = 1

namespace TimeDirection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (τ : TimeDirection E)

attribute [simp] TimeDirection.norm_eq_one

@[ext]
lemma ext {τ₁ τ₂ : TimeDirection E} (h : τ₁.vec = τ₂.vec) : τ₁ = τ₂ := by
  cases τ₁
  cases τ₂
  cases h
  rfl

/-- Time-coordinate functional associated to `τ`. -/
def timeCoord : E →L[ℝ] ℝ :=
  innerSL ℝ τ.vec

lemma timeCoord_apply (x : E) : τ.timeCoord x = (innerSL ℝ τ.vec) x := rfl

lemma timeCoord_vec : τ.timeCoord τ.vec = 1 := by
  simp [TimeDirection.timeCoord, τ.norm_eq_one]

lemma timeCoord_smul_vec (t : ℝ) : τ.timeCoord (t • τ.vec) = t := by
  simp [τ.timeCoord_vec]

/-!
## B. Translations along the time direction
-/

/-- Scalar-time translation along the distinguished direction `τ.vec`. -/
def translateAlong (t : ℝ) (x : E) : E :=
  x + t • τ.vec

lemma translateAlong_apply (t : ℝ) (x : E) : τ.translateAlong t x = x + t • τ.vec := rfl

@[simp]
lemma translateAlong_zero (x : E) : τ.translateAlong 0 x = x := by
  simp [translateAlong]

@[simp]
lemma translateAlong_add (s t : ℝ) (x : E) :
    τ.translateAlong (s + t) x = τ.translateAlong s (τ.translateAlong t x) := by
  simp [translateAlong, add_smul, add_left_comm, add_comm]

@[simp]
lemma translateAlong_neg_cancel (t : ℝ) (x : E) :
    τ.translateAlong (-t) (τ.translateAlong t x) = x := by
  simp [translateAlong, add_assoc]

lemma timeCoord_translateAlong (t : ℝ) (x : E) :
    τ.timeCoord (τ.translateAlong t x) = τ.timeCoord x + t := by
  calc
    τ.timeCoord (τ.translateAlong t x)
        = τ.timeCoord x + τ.timeCoord (t • τ.vec) := by
            simp [TimeDirection.translateAlong, map_add]
    _ = τ.timeCoord x + t := by simp [τ.timeCoord_smul_vec]

/-- Translation along `τ.vec` preserves Lebesgue measure. -/
lemma translateAlong_measurePreserving
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (t : ℝ) :
    MeasurePreserving (τ.translateAlong t) (volume : Measure E) (volume : Measure E) := by
  refine ⟨(continuous_id.add continuous_const).measurable, ?_⟩
  simpa [translateAlong] using map_add_right_eq_self (volume : Measure E) (t • τ.vec)

/-!
## D. Induced actions on Schwartz test functions
-/

private lemma sub_const_hasTemperateGrowth (a : E) :
    Function.HasTemperateGrowth (fun x : E => x - a) := by
  fun_prop

variable {E : Type*} [NormedAddCommGroup E]

private lemma sub_const_antilipschitz (a : E) :
    AntilipschitzWith (1 : NNReal) (fun x : E => x - a) := by
  have hIso : Isometry (fun x : E => x - a) := by
    intro x y
    simp
  simpa using hIso.antilipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (τ : TimeDirection E)

/-- Translation `f(x) ↦ f(x - t • τ.vec)` as a continuous linear map on Schwartz maps. -/
def translateAlongTestFunction {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (t : ℝ) :
    SchwartzMap E F →L[𝕜] SchwartzMap E F :=
  SchwartzMap.compCLMOfAntilipschitz (𝕜 := 𝕜)
    (D := E) (E := E) (F := F)
    (g := fun x : E => x - t • τ.vec)
    (sub_const_hasTemperateGrowth (E := E) (t • τ.vec))
    (sub_const_antilipschitz (E := E) (t • τ.vec))

@[simp]
lemma translateAlongTestFunction_apply {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (t : ℝ) (f : SchwartzMap E F) (x : E) :
    τ.translateAlongTestFunction (𝕜 := 𝕜) (F := F) t f x = f (x - t • τ.vec) := by
  simp [TimeDirection.translateAlongTestFunction]

@[simp]
lemma translateAlongTestFunction_zero {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] :
    τ.translateAlongTestFunction (𝕜 := 𝕜) (F := F) 0 =
      ContinuousLinearMap.id 𝕜 (SchwartzMap E F) := by
  ext f x
  simp

lemma translateAlongTestFunction_add {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (s t : ℝ) :
    τ.translateAlongTestFunction (𝕜 := 𝕜) (F := F) (s + t) =
      (τ.translateAlongTestFunction (𝕜 := 𝕜) (F := F) s).comp
        (τ.translateAlongTestFunction (𝕜 := 𝕜) (F := F) t) := by
  ext f x
  simp [sub_eq_add_neg, add_smul, add_assoc, add_comm]

/-- Nonnegative-time half-space associated to `τ`. -/
def nonnegativeHalfSpace : Set E :=
  {x | 0 ≤ τ.timeCoord x}

/-- Nonpositive-time half-space associated to `τ`. -/
def nonpositiveHalfSpace : Set E :=
  {x | τ.timeCoord x ≤ 0}

@[simp]
lemma mem_nonnegativeHalfSpace (x : E) :
    x ∈ τ.nonnegativeHalfSpace ↔ 0 ≤ τ.timeCoord x := Iff.rfl

@[simp]
lemma mem_nonpositiveHalfSpace (x : E) :
    x ∈ τ.nonpositiveHalfSpace ↔ τ.timeCoord x ≤ 0 := Iff.rfl

end TimeDirection

/-!
## C. Reflection operations and half-spaces
-/

/-- Reflection data compatible with a chosen time direction. -/
structure TimeDirectionOps (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (τ : TimeDirection E) where
  /-- Reflection map (as a linear isometry). -/
  reflect : E ≃ₗᵢ[ℝ] E
  /-- Reflection flips the `τ`-time coordinate. -/
  reflect_timeCoord : ∀ x : E, τ.timeCoord (reflect x) = - τ.timeCoord x
  /-- Reflection is pointwise involutive. -/
  reflect_involutive : ∀ x : E, reflect (reflect x) = x
  /-- Reflection fixes the hyperplane orthogonal to `τ`. -/
  reflect_fix_hyperplane : ∀ x : E, τ.timeCoord x = 0 → reflect x = x

attribute [simp] TimeDirectionOps.reflect_timeCoord TimeDirectionOps.reflect_involutive

namespace TimeDirectionOps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {τ : TimeDirection E} (ops : TimeDirectionOps E τ)

lemma reflect_mem_nonnegative_iff (x : E) :
    ops.reflect x ∈ τ.nonnegativeHalfSpace ↔ x ∈ τ.nonpositiveHalfSpace := by
  simp [TimeDirection.nonnegativeHalfSpace, TimeDirection.nonpositiveHalfSpace, ops.reflect_timeCoord]

lemma reflect_mem_nonpositive_iff (x : E) :
    ops.reflect x ∈ τ.nonpositiveHalfSpace ↔ x ∈ τ.nonnegativeHalfSpace := by
  simp [TimeDirection.nonnegativeHalfSpace, TimeDirection.nonpositiveHalfSpace, ops.reflect_timeCoord]

/-- Reflection preserves Lebesgue measure. -/
lemma reflect_measurePreserving
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    MeasurePreserving ops.reflect (volume : Measure E) (volume : Measure E) := by
  simpa using ops.reflect.measurePreserving

/-- Reflection action on Schwartz functions (any `RCLike 𝕜`). -/
def reflectTestFunction {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    [FiniteDimensional ℝ E] :
    SchwartzMap E F →L[𝕜] SchwartzMap E F :=
  SchwartzMap.compCLMOfContinuousLinearEquiv (𝕜 := 𝕜)
    (D := E) (E := E) (F := F)
    (g := ops.reflect.toContinuousLinearEquiv)

@[simp]
lemma reflectTestFunction_apply {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    [FiniteDimensional ℝ E] (f : SchwartzMap E F) (x : E) :
    ops.reflectTestFunction (𝕜 := 𝕜) (F := F) f x = f (ops.reflect x) := rfl

@[simp]
lemma reflectTestFunction_involutive {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    [FiniteDimensional ℝ E] (f : SchwartzMap E F) :
    ops.reflectTestFunction (𝕜 := 𝕜) (F := F)
        (ops.reflectTestFunction (𝕜 := 𝕜) (F := F) f) = f := by
  ext x
  simp

end TimeDirectionOps

/-!
## Examples

-/

section Examples

example : ∃ τ : TimeDirection ℝ, τ.timeCoord (1 : ℝ) = 1 := by
  refine ⟨⟨(1 : ℝ), by simp⟩, ?_⟩
  simp [TimeDirection.timeCoord]

example (t x : ℝ) :
    let τ : TimeDirection ℝ := ⟨(1 : ℝ), by simp⟩
    τ.translateAlong t x = x + t := by
  simp [TimeDirection.translateAlong]

example :
    ∃ τ : TimeDirection ℝ, ∃ ops : TimeDirectionOps ℝ τ, ops.reflect (2 : ℝ) = -2 := by
  refine ⟨⟨(1 : ℝ), by simp⟩, ?_⟩
  refine ⟨{
    reflect := {
      toLinearEquiv := LinearEquiv.neg ℝ
      norm_map' := by intro x; simp
    }
    reflect_timeCoord := by intro x; simp [TimeDirection.timeCoord]
    reflect_involutive := by intro x; simp
    reflect_fix_hyperplane := by
      intro x hx
      have : x = 0 := by simpa [TimeDirection.timeCoord] using hx
      simp [this]
  }, by simp⟩

example (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    let τ : TimeDirection ℝ := ⟨(1 : ℝ), by simp⟩
    let ops : TimeDirectionOps ℝ τ := {
      reflect := {
        toLinearEquiv := LinearEquiv.neg ℝ
        norm_map' := by intro y; simp
      }
      reflect_timeCoord := by intro y; simp [TimeDirection.timeCoord]
      reflect_involutive := by intro y; simp
      reflect_fix_hyperplane := by
        intro y hy
        have : y = 0 := by simpa [TimeDirection.timeCoord, τ] using hy
        simp [this]
    }
    ops.reflectTestFunction (𝕜 := ℝ) f x = f (-x) := by
  simp [TimeDirectionOps.reflectTestFunction]

end Examples

end SpaceTime
