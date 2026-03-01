/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.GFF.PackageOS0
import OSforGFF.GFF.PackageProved
import OSforGFF.OS0_GFF

/-!
## The proved free GFF package satisfies OS0

This instantiates `GFF.PackageOS0` for the Kolmogorov+nuclear-support measure construction.
-/

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

/-- The proved package, upgraded with the OS0 analyticity theorem. -/
noncomputable def packageOS0Proved (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    PackageOS0 (m := m) :=
  { (packageProved (m := m)) with
    os0 := by
      simpa [gaussianFreeField_free, μ_GFF] using
        (QFT.gaussianFreeField_satisfies_OS0 (m := m)) }

end
end GFF
end OSforGFF
