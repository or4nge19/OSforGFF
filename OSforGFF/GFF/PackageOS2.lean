import OSforGFF.GFF.PackageOS1

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

variable (m : ℝ) [Fact (0 < m)]

/-- Extension of `GFF.PackageOS1` by OS2 Euclidean invariance. -/
structure PackageOS2 extends PackageOS1 (m := m) where
  os2 : OS2_EuclideanInvariance μ

end
end GFF
end OSforGFF

