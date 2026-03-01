import OSforGFF.GFF.PackageOS2

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

variable (m : ℝ) [Fact (0 < m)]

/-- Extension of `GFF.PackageOS2` by OS3 reflection positivity. -/
structure PackageOS3 extends PackageOS2 (m := m) where
  os3 : OS3_ReflectionPositivity μ

end
end GFF
end OSforGFF

