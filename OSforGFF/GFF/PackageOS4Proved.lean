import OSforGFF.GFF.PackageOS4
import OSforGFF.GFF.PackageOS3Proved
import OSforGFF.OS4_Clustering
import OSforGFF.OS4_Ergodicity

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

/-- The proved free-field backend packaged as `GFF.PackageOS4`. -/
noncomputable def packageOS4Proved (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    PackageOS4 (m := m) :=
  { (packageOS3Proved (m := m)) with
    os4_clustering := by
      simpa using (QFT.gaussianFreeField_satisfies_OS4 (m := m))
    os4_ergodicity := by
      -- Polynomial clustering (α=6) implies ergodicity.
      exact OS4_Ergodicity.OS4_PolynomialClustering_implies_OS4_Ergodicity (m := m)
        (QFT.gaussianFreeField_satisfies_OS4_PolynomialClustering (m := m) 6 (by norm_num)) }

end
end GFF
end OSforGFF

