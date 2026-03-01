/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.QFT.LatticeGauge.GaugeTransform

/-!
# Lattice gauge theory: abelian identities

This file contains statements that require commutativity in the gauge group,
and are therefore separated from the noncommutative core.
-/

set_option autoImplicit false

namespace PhysLean
namespace QFT
namespace LatticeGauge

open LatticePoint

universe u

variable {d : ℕ} {G : Type u}

section Group

variable [Group G]

/-- Reversing the orientation of a plaquette results in the inverse Wilson loop. -/
lemma wilsonLoop_swap_eq_inv (U : GaugeField d G) (p : LatticePoint d)
    {μ ν : Fin d} (h : μ ≠ ν) :
    wilsonLoop U p ν μ (Ne.symm h) = (wilsonLoop U p μ ν h)⁻¹ := by
  rw [wilsonLoop_expansion, wilsonLoop_expansion]
  group

end Group

end LatticeGauge
end QFT
end PhysLean
