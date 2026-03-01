/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Minimal Gel'fand triple API `N ⊂ H ⊂ N'`

This file introduces an abstraction for a Gel'fand triple
`N ⊂ H ⊂ N'`, where the dual `N'` is represented as `WeakDual ℝ N`.

This only provides the core data and canonical maps (notably the embedding `H → N'`).
Any Minlos/Gaussian measure existence theorems should live in separate modules which
assume the required hypotheses (e.g. nuclearity).
-/

namespace PhysLean
namespace QFT
namespace Minlos

noncomputable section

open scoped RealInnerProductSpace

/-- A minimal Gel'fand triple API `N ⊂ H ⊂ N'`.

`toHilbert` is the canonical continuous embedding of test vectors into the
pivot Hilbert space. The dual `N'` is modeled by `WeakDual ℝ N`. -/
structure GelfandTriple where
  N : Type*
  H : Type*
  [instAddCommGroupN : AddCommGroup N]
  [instModuleN : Module ℝ N]
  [instTopologicalSpaceN : TopologicalSpace N]
  [instNormedAddCommGroupH : NormedAddCommGroup H]
  [instInnerProductSpaceH : InnerProductSpace ℝ H]
  toHilbert : N →L[ℝ] H

attribute [instance] GelfandTriple.instAddCommGroupN
attribute [instance] GelfandTriple.instModuleN
attribute [instance] GelfandTriple.instTopologicalSpaceN
attribute [instance] GelfandTriple.instNormedAddCommGroupH
attribute [instance] GelfandTriple.instInnerProductSpaceH

namespace GelfandTriple

variable (T : GelfandTriple)

/-- The distribution space `N'` represented by the weak dual. -/
abbrev DualSpace := WeakDual ℝ T.N

/-- Optional hypothesis: the embedding `toHilbert : N → H` has dense range. -/
class ToHilbertDenseRange (T : GelfandTriple) : Prop where
  dense_range : DenseRange T.toHilbert

lemma denseRange_toHilbert (T : GelfandTriple) [ToHilbertDenseRange T] :
    DenseRange T.toHilbert :=
  ToHilbertDenseRange.dense_range (T := T)

/-- Diagonal “covariance” induced by the embedding `N → H` (purely as a norm-square). -/
def covarianceDiagonal (f : T.N) : ℝ :=
  ‖T.toHilbert f‖ ^ (2 : ℕ)

lemma continuous_covarianceDiagonal :
    Continuous fun f : T.N => (T.covarianceDiagonal f : ℝ) := by
  have hnorm : Continuous fun f : T.N => ‖T.toHilbert f‖ :=
    Continuous.norm T.toHilbert.continuous
  simpa [covarianceDiagonal] using (Continuous.pow hnorm 2)

lemma covarianceDiagonal_nonneg (f : T.N) : 0 ≤ T.covarianceDiagonal f := by
  simp [covarianceDiagonal]

/-!
## Canonical embedding `H → N'`

Given `toHilbert : N →L[ℝ] H`, any `h : H` defines a continuous linear functional on `N` by
`n ↦ ⟪h, toHilbert n⟫`. This yields the canonical map `H → WeakDual ℝ N`.
-/

/-- The canonical map `H → N'` induced by the embedding `N → H`. -/
noncomputable def dualEmbedding : T.H →L[ℝ] WeakDual ℝ T.N :=
  { toFun := fun h =>
      (innerSL ℝ h).comp T.toHilbert
    map_add' := by
      intro h₁ h₂
      apply DFunLike.ext
      intro n
      simp
    map_smul' := by
      intro c h
      apply DFunLike.ext
      intro n
      simp
    cont := by
      refine WeakDual.continuous_of_continuous_eval (𝕜 := ℝ) (E := T.N) ?_
      intro n
      simpa [innerSLFlip_apply_apply] using
        (innerSLFlip ℝ (E := T.H) (T.toHilbert n)).continuous }

@[simp]
lemma dualEmbedding_apply (h : T.H) (n : T.N) :
    T.dualEmbedding h n = ⟪h, T.toHilbert n⟫ := by
  rfl

end GelfandTriple

end

end Minlos
end QFT
end PhysLean
