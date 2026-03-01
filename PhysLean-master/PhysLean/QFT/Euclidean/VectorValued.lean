/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.Algebra.Module.WeakDual

/-!
# Vector-valued Schwartz test functions and distribution spaces

This module provides reusable aliases and basic operations for **vector-valued** Schwartz spaces
and their weak duals, intended as a minimal abstraction layer for internal symmetries (e.g. global
gauge rotations) in Euclidean QFT formalizations.
-/

namespace PhysLean
namespace QFT
namespace Spacetime

open scoped BigOperators

section VectorValuedQFT

open SchwartzMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V]
  [SMulCommClass ℝ 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [SMulCommClass ℝ 𝕜 W]

/-- The space of `V`-valued Schwartz test functions on `E`, viewed as a `𝕜`-module. -/
abbrev VectorTestFunction (𝕜 : Type*) (E : Type*) (V : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V] :=
  SchwartzMap E V

/-- The weak-dual distribution space on vector-valued test functions. -/
abbrev VectorFieldConfiguration (𝕜 : Type*) (E : Type*) (V : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V] :=
  WeakDual 𝕜 (VectorTestFunction 𝕜 E V)

namespace WeakDual

section Comap

variable {𝕜 : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜]
variable {E F : Type*} [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/-- Contravariant action of a continuous linear map on weak duals by precomposition. -/
noncomputable def comap (L : E →L[𝕜] F) : WeakDual 𝕜 F →L[𝕜] WeakDual 𝕜 E :=
  { toFun := fun ω => ω.comp L
    map_add' := by
      intro ω₁ ω₂
      rfl
    map_smul' := by
      intro c ω
      rfl
    cont := by
      refine WeakDual.continuous_of_continuous_eval (𝕜 := 𝕜) (E := E)
        (g := fun ω : WeakDual 𝕜 F => (ω.comp L : WeakDual 𝕜 E)) ?_
      intro e
      simpa using (WeakDual.eval_continuous (𝕜 := 𝕜) (E := F) (L e)) }

@[simp]
lemma comap_apply (L : E →L[𝕜] F) (ω : WeakDual 𝕜 F) (e : E) :
    comap (𝕜 := 𝕜) L ω e = ω (L e) :=
  rfl

end Comap

end WeakDual

/-!
## Pairing (distributions acting on test functions)

For `ω : VectorFieldConfiguration 𝕜 E V = WeakDual 𝕜 𝓢(E, V)` and `f : 𝓢(E, V)`, the pairing is
just evaluation `ω f : 𝕜`. We also expose this as a continuous linear map in `ω` for fixed `f`.
-/

/-- The basic pairing `⟪ω, f⟫ := ω f`. -/
def distributionPairing (ω : VectorFieldConfiguration 𝕜 E V) (f : VectorTestFunction 𝕜 E V) : 𝕜 :=
  ω f

@[simp]
lemma distributionPairing_apply (ω : VectorFieldConfiguration 𝕜 E V)
    (f : VectorTestFunction 𝕜 E V) :
    distributionPairing (𝕜 := 𝕜) (E := E) (V := V) ω f = ω f :=
  rfl

@[simp]
lemma distributionPairing_add (ω₁ ω₂ : VectorFieldConfiguration 𝕜 E V)
    (f : VectorTestFunction 𝕜 E V) :
    distributionPairing (𝕜 := 𝕜) (E := E) (V := V) (ω₁ + ω₂) f =
      distributionPairing (𝕜 := 𝕜) (E := E) (V := V) ω₁ f +
        distributionPairing (𝕜 := 𝕜) (E := E) (V := V) ω₂ f :=
  rfl

@[simp]
lemma distributionPairing_smul (c : 𝕜) (ω : VectorFieldConfiguration 𝕜 E V)
    (f : VectorTestFunction 𝕜 E V) :
    distributionPairing (𝕜 := 𝕜) (E := E) (V := V) (c • ω) f =
      c * distributionPairing (𝕜 := 𝕜) (E := E) (V := V) ω f :=
  rfl

/-- Evaluation at a test function as a continuous linear map `ω ↦ ω f`. -/
@[simp]
def distributionPairingCLM (f : VectorTestFunction 𝕜 E V) :
    VectorFieldConfiguration 𝕜 E V →L[𝕜] 𝕜 where
  toFun ω := distributionPairing (𝕜 := 𝕜) (E := E) (V := V) ω f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := WeakDual.eval_continuous (𝕜 := 𝕜) (E := VectorTestFunction 𝕜 E V) f

@[simp]
lemma distributionPairingCLM_apply (f : VectorTestFunction 𝕜 E V)
    (ω : VectorFieldConfiguration 𝕜 E V) :
    distributionPairingCLM (𝕜 := 𝕜) (E := E) (V := V) f ω =
      distributionPairing (𝕜 := 𝕜) (E := E) (V := V) ω f :=
  rfl

/-!
## Lifting internal symmetries

If `A : V →L[𝕜] W` is a continuous linear map (a constant “internal symmetry” acting on the target
space), we can apply it pointwise to a Schwartz function `f : 𝓢(E, V)` to obtain a Schwartz
function `A ∘ f : 𝓢(E, W)`. This lifts to a continuous linear map on Schwartz spaces, and then
dually to a continuous linear map on weak duals by precomposition.
-/

/-- Lift a target-space map `A : V →L[𝕜] W` to a continuous linear map on Schwartz spaces. -/
noncomputable def liftInternalSymmetry (A : V →L[𝕜] W) :
    VectorTestFunction 𝕜 E V →L[𝕜] VectorTestFunction 𝕜 E W := by
  refine SchwartzMap.mkCLM (𝕜 := 𝕜) (D := E) (E := V) (F := E) (G := W)
    (fun f x => A (f x))
    (fun f g x => by simp)
    (fun c f x => by simp)
    (fun f => by
      simpa using ContDiff.comp (A.restrictScalars ℝ).contDiff f.smooth')
    (by
      rintro ⟨k, n⟩
      refine ⟨{(k, n)}, ‖(A.restrictScalars ℝ)‖, by positivity, ?_⟩
      intro f x
      simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
      have h_deriv :
          iteratedFDeriv ℝ n (fun y => (A.restrictScalars ℝ) (f y)) x =
            (A.restrictScalars ℝ).compContinuousMultilinearMap (iteratedFDeriv ℝ n f x) :=
        ContinuousLinearMap.iteratedFDeriv_comp_left (A.restrictScalars ℝ)
          (f.smooth _).contDiffAt (WithTop.coe_le_coe.mpr le_top)
      have hx :
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => (A.restrictScalars ℝ) (f y)) x‖
            ≤ ‖(A.restrictScalars ℝ)‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
        rw [h_deriv]
        calc
          ‖x‖ ^ k *
              ‖(A.restrictScalars ℝ).compContinuousMultilinearMap (iteratedFDeriv ℝ n f x)‖
              ≤ ‖x‖ ^ k * (‖(A.restrictScalars ℝ)‖ * ‖iteratedFDeriv ℝ n f x‖) := by
                  apply mul_le_mul_of_nonneg_left
                  · exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le
                      (A.restrictScalars ℝ) _
                  · exact pow_nonneg (norm_nonneg _) _
          _ = ‖(A.restrictScalars ℝ)‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by ring
      calc
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => (A.restrictScalars ℝ) (f y)) x‖
            ≤ ‖(A.restrictScalars ℝ)‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := hx
        _ ≤ ‖(A.restrictScalars ℝ)‖ * SchwartzMap.seminorm 𝕜 k n f := by
              gcongr
              exact le_seminorm (𝕜 := 𝕜) (k := k) (n := n) f x
        _ = ‖(A.restrictScalars ℝ)‖ * schwartzSeminormFamily 𝕜 E V (k, n) f := by
              simp [schwartzSeminormFamily_apply])

/-- Dual action on distributions: precompose with the lifted test-function map. -/
noncomputable def liftInternalSymmetryDual (A : V →L[𝕜] W) :
    VectorFieldConfiguration 𝕜 E W →L[𝕜] VectorFieldConfiguration 𝕜 E V :=
  WeakDual.comap (𝕜 := 𝕜) (E := VectorTestFunction 𝕜 E V) (F := VectorTestFunction 𝕜 E W)
    (liftInternalSymmetry (𝕜 := 𝕜) (E := E) A)

@[simp]
lemma liftInternalSymmetry_apply (A : V →L[𝕜] W) (f : VectorTestFunction 𝕜 E V) (x : E) :
    liftInternalSymmetry (𝕜 := 𝕜) (E := E) A f x = A (f x) := by
  rfl

@[simp]
lemma liftInternalSymmetryDual_apply (A : V →L[𝕜] W)
    (ω : VectorFieldConfiguration 𝕜 E W) (f : VectorTestFunction 𝕜 E V) :
    liftInternalSymmetryDual (𝕜 := 𝕜) (E := E) A ω f =
      ω (liftInternalSymmetry (𝕜 := 𝕜) (E := E) A f) := by
  rfl

@[simp]
lemma distributionPairing_liftInternalSymmetryDual (A : V →L[𝕜] W)
    (ω : VectorFieldConfiguration 𝕜 E W) (f : VectorTestFunction 𝕜 E V) :
    distributionPairing (𝕜 := 𝕜) (E := E) (V := V)
        (liftInternalSymmetryDual (𝕜 := 𝕜) (E := E) A ω) f
      =
    distributionPairing (𝕜 := 𝕜) (E := E) (V := W) ω
        (liftInternalSymmetry (𝕜 := 𝕜) (E := E) A f) := by
  rfl

end VectorValuedQFT

end Spacetime
end QFT
end PhysLean
