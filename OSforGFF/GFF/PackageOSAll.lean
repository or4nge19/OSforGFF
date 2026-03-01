import OSforGFF.GFF.PackageOS4
import OSforGFF.GFF.OS1

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

namespace PackageOS4

variable {m : ℝ} [Fact (0 < m)]
variable (P : PackageOS4 (m := m))

/-- Bundle OS0–OS4 from a `GFF.PackageOS4`.

This is the main “integration joint”: any backend (the proved Kolmogorov+nuclear-support one,
or an external `gaussian-field` construction) only needs to provide a `PackageOS4` instance, and
all downstream OS-facing code can be written against this stable interface. -/
theorem satisfiesAllOS : SatisfiesAllOS P.μ where
  os0 := P.toPackageOS0.os0
  os1 := PackageOS1.os1 (m := m) (P := P.toPackageOS1)
  os2 := P.os2
  os3 := P.os3
  os4_clustering := P.os4_clustering
  os4_ergodicity := P.os4_ergodicity

end PackageOS4

end
end GFF
end OSforGFF

