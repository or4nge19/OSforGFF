/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Minimal Euclidean QFT model container

This is a tiny reusable wrapper: a probability measure on field configurations together with
a proof that it satisfies an axiom bundle `Satisfies`.

Downstream developments can plug in their own `Satisfies` predicate (OS axioms, Euclidean
invariance, clustering, etc.) without committing to any specific representation of the field.
-/

open MeasureTheory

namespace PhysLean
namespace QFT

universe u

/-- A minimal “model” container: a probability measure together with a proof that it satisfies
some axiom bundle `Satisfies`. -/
structure EuclideanQFTModel
    (FieldConfiguration : Type u) [MeasurableSpace FieldConfiguration]
    (Satisfies : ProbabilityMeasure FieldConfiguration → Prop) : Type (u + 1) where
  μ : ProbabilityMeasure FieldConfiguration
  satisfies : Satisfies μ

end QFT
end PhysLean
