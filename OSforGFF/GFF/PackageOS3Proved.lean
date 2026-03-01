import OSforGFF.GFF.PackageOS3
import OSforGFF.GFF.PackageOS2Proved
import OSforGFF.OS3_GFF

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

/-- The proved free-field backend packaged as `GFF.PackageOS3`. -/
noncomputable def packageOS3Proved (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    PackageOS3 (m := m) :=
  { (packageOS2Proved (m := m)) with
    os3 := by
      simpa using (QFT.gaussianFreeField_OS3_real (m := m)) }

end
end GFF
end OSforGFF

