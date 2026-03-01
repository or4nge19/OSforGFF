/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.SpaceAndTime.SpaceTime.TimeDirection

/-!
# Coordinate-free Euclidean time direction API

This module provides the minimal coordinate-free data needed for OS-style time evolution:

- a distinguished unit direction `e` in an ambient Euclidean space `E`,
- scalar-time translations `x ↦ x + t • e`,
- a reflection operator compatible with that time coordinate,
- induced actions on Schwartz test functions.

The goal is to decouple OS-axiom statements from hard-coded coordinate indices.
-/

namespace OSforGFF
namespace Spacetime

-- This file is a compatibility layer: the canonical OS time-direction interface lives in PhysLean
-- (and uses the `SpaceTime` namespace). We keep the historical `OSforGFF.Spacetime.*` names as
-- abbreviations.

abbrev TimeDirection (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  SpaceTime.TimeDirection E

abbrev TimeDirectionOps (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (τ : TimeDirection E) :=
  SpaceTime.TimeDirectionOps E τ

end Spacetime
end OSforGFF
