/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.GFF.PackageOS0Proved
import OSforGFF.GFF.ComplexCharacteristic
import OSforGFF.GFFMconstruct

/-!
## Specializing the package-level theorem to the proved GFF measure

This file instantiates the backend-agnostic OS0 continuation theorem
for the concrete (proved) free GFF measure `gaussianFreeField_free`.
-/

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

theorem gff_complex_characteristic_OS0_proved (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    ∀ J : TestFunctionℂ,
      GJGeneratingFunctionalℂ (gaussianFreeField_free m) J =
        Complex.exp (-(1 / 2 : ℂ) * freeCovarianceℂ_bilinear m J J) := by
  intro J
  simpa [packageOS0Proved, packageProved, gaussianFreeField_free] using
    (PackageOS0.gff_complex_characteristic_OS0 (m := m) (P := packageOS0Proved (m := m)) J)

end
end GFF
end OSforGFF
