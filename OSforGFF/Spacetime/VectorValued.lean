/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.QFT.Euclidean.VectorValued

/-!
# Vector-valued Schwartz test functions and distribution spaces (compatibility layer)

The canonical development of this API lives in PhysLean under `PhysLean.QFT.Spacetime`.
This file re-exports the same names into `OSforGFF.Spacetime` to avoid duplication and to ease
downstream migration.
-/

namespace OSforGFF
namespace Spacetime

export PhysLean.QFT.Spacetime
  (VectorTestFunction VectorFieldConfiguration
   distributionPairing distributionPairing_apply distributionPairing_add distributionPairing_smul
   distributionPairingCLM distributionPairingCLM_apply
   liftInternalSymmetry liftInternalSymmetryDual
   liftInternalSymmetry_apply liftInternalSymmetryDual_apply distributionPairing_liftInternalSymmetryDual)

namespace WeakDual
export PhysLean.QFT.Spacetime.WeakDual (comap comap_apply)
end WeakDual

end Spacetime
end OSforGFF

