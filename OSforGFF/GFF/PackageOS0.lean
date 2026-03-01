/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.GFF.Package
import OSforGFF.OS_Axioms

/-!
## Extending `GFF.Package` with OS0 analyticity

Downstream “complex Gaussianity” results (e.g. `GFFIsGaussian`) use OS0 to justify differentiating
under the integral sign. This file packages that additional hypothesis.
-/

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

variable (m : ℝ) [Fact (0 < m)]

/-- A free massive GFF package together with OS0 analyticity of its generating functional. -/
structure PackageOS0 extends Package (m := m) where
  os0 : OS0_Analyticity μ

end
end GFF
end OSforGFF

