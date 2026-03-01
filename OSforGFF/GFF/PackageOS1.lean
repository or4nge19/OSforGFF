import OSforGFF.OS_Axioms
import OSforGFF.GFF.PackageOS0

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

variable (m : ℝ) [Fact (0 < m)]

/-- Extension of `GFF.PackageOS0` by the extra `TwoPointIntegrable` obligation required by
`OS1_Regularity` when choosing `p = 2`.

This keeps OS1 proofs and downstream OS4 infrastructure package-parametric, while letting each
backend discharge two-point local integrability using whatever analytic technology it provides. -/
structure PackageOS1 extends PackageOS0 (m := m) where
  twoPointIntegrable : TwoPointIntegrable μ

end
end GFF
end OSforGFF
