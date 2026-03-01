/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.GFF.Package
import OSforGFF.GFFMconstructProved

/-!
## The proved Kolmogorov+nuclear-support free GFF as a `OSforGFF.GFF.Package`
-/

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

/-- The proved free GFF (Kolmogorov + nuclear support) packaged behind the `GFF.Package`
interface. -/
noncomputable def packageProved (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    Package (m := m) :=
  { μ := QFT.GFFMconstructProved.gaussianFreeField_free_proved (m := m)
    gff_real_characteristic := QFT.GFFMconstructProved.gff_real_characteristic_proved (m := m) }

end
end GFF
end OSforGFF

