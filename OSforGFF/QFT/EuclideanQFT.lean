/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PhysLean.QFT.Euclidean.Model

/-!
## Minimal Euclidean-QFT “model container”

This file defines a **tiny** container structure intended to be reusable across projects
(including PhysLean-facing integrations) without importing any of the heavy OS/GFF development.

Downstream projects should instantiate this with:

- a concrete `FieldConfiguration` type (with a `MeasurableSpace` instance), and
- a predicate `Satisfies : ProbabilityMeasure FieldConfiguration → Prop` collecting the axioms.
-/

namespace QFT

-- Compatibility layer: the canonical container lives in PhysLean.
abbrev EuclideanQFTModel := PhysLean.QFT.EuclideanQFTModel

end QFT

