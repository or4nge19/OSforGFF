/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.Basic
import OSforGFF.CovarianceR

/-!
## A small “GFF package” interface

Many downstream results (OS0 analyticity, Gaussian moments, Gaussianity of the generating
functional, …) only need:

- a probability measure on `FieldConfiguration`, and
- the real characteristic-functional identity with covariance `freeCovarianceFormR`.

This file packages exactly that data as a structure, so we can later plug in different
measure-construction backends (e.g. Minlos-based vs Kolmogorov+nuclear-support) without changing
the OS-axiom-facing theory files.
-/

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

variable (m : ℝ) [Fact (0 < m)]

/-- A free massive GFF measure on `FieldConfiguration` together with its real characteristic
functional. -/
structure Package where
  /-- The probability measure on field configurations (tempered distributions). -/
  μ : ProbabilityMeasure FieldConfiguration
  /-- Real characteristic functional: \(Z[f] = \exp(-\tfrac12\,Q(f,f))\). -/
  gff_real_characteristic :
    ∀ f : TestFunction,
      GJGeneratingFunctional μ f =
        Complex.exp (-(1 / 2 : ℂ) * (freeCovarianceFormR m f f : ℝ))

attribute [simp] Package.gff_real_characteristic

end
end GFF
end OSforGFF

