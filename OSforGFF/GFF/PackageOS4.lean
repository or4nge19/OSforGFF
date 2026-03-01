import OSforGFF.GFF.PackageOS3

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

variable (m : ℝ) [Fact (0 < m)]

/-- Extension of `GFF.PackageOS3` by OS4 clustering and ergodicity. -/
structure PackageOS4 extends PackageOS3 (m := m) where
  os4_clustering : OS4_Clustering μ
  os4_ergodicity : OS4_Ergodicity μ

end
end GFF
end OSforGFF

