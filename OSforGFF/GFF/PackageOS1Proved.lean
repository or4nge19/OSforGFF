import OSforGFF.GFF.PackageOS1
import OSforGFF.GFF.PackageOS0Proved
import OSforGFF.GFF.OS1
import OSforGFF.OS1_GFF

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

/-- The proved free-field backend packaged as `GFF.PackageOS1`.

This combines:
- the proved measure + real characteristic functional (`packageOS0Proved`), and
- the (p = 2) two-point local integrability lemma from `OS1_GFF.lean`. -/
noncomputable def packageOS1Proved (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    PackageOS1 (m := m) :=
  { (packageOS0Proved (m := m)) with
    twoPointIntegrable := by
      simpa using (gff_two_point_locally_integrable (m := m)) }

end
end GFF
end OSforGFF
