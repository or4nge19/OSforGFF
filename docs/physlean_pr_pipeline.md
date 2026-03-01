# PhysLean PR pipeline (from this workspace)

This document stages **reviewable, idiomatic** PRs to PhysLean that extract the most reusable,
axiom-free parts of the `OSforGFF` development, while keeping the proved `OSforGFF` package
self-contained.

Guiding principles:

- **Small PRs** (one conceptual API per PR).
- **No `sorry` / `axiom` / semantic gaps** in the extracted surface.
- **Mathlib-first** for general lemmas; PhysLean for “physics-shaped” interfaces.
- Prefer **coordinate-free** interfaces (time direction, internal symmetries, Gelfand triples).
- For distribution-valued fields, prefer the **cylindrical σ-algebra** on `WeakDual` as the default.

## Proposed PR sequence (high confidence)

### PR A: Cylindrical measurable space on `WeakDual` (core probability interface)

- **Files**
  - `PhysLean/Mathematics/Distribution/WeakDualMeasurable.lean`
- **API**
  - `instance instMeasurableSpaceWeakDual : MeasurableSpace (WeakDual 𝕜 E)`
  - `measurable_weakDual_toFun`
  - `measurable_weakDual_eval`
  - `weakDual_measurable_of_eval_measurable`
- **Rationale**
  - This is the minimal, assumption-light σ-algebra needed for Minlos/Gaussian constructions.
  - Avoids implicitly requiring `BorelSpace (WeakDual 𝕜 E)` in applications.

### PR B: Minimal Euclidean QFT “model container”

- **Files**
  - `PhysLean/QFT/Euclidean/Model.lean`
- **API**
  - `QFT.EuclideanQFTModel FieldConfiguration Satisfies`
- **Rationale**
  - Separates “model container” from “axiom bundle”, matching PhysLean style.

### PR C: Coordinate-free time direction + reflection/translation on Schwartz test functions

- **Files**
  - `PhysLean/QFT/Euclidean/TimeDirection.lean`
- **API**
  - `Spacetime.TimeDirection`, `Spacetime.TimeDirectionOps`
  - `TimeDirection.timeCoord`, `TimeDirection.translateAlong`
  - `TimeDirectionOps.reflectTestFunction`, `translateAlongTestFunction`
- **Rationale**
  - Lets OS-style axioms be stated without fixed coordinate projections.

### PR D: Vector-valued Schwartz test functions and distributions + internal symmetries

- **Files**
  - `PhysLean/QFT/Euclidean/VectorValued.lean`
- **API**
  - `Spacetime.VectorTestFunction`, `Spacetime.VectorFieldConfiguration`
  - `WeakDual.comap`
  - `distributionPairing`, `distributionPairingCLM`
  - `liftInternalSymmetry`, `liftInternalSymmetryDual`

### PR E: Minimal Gel'fand triple interface (`N ⊂ H ⊂ N'`)

- **Files**
  - `PhysLean/QFT/Euclidean/GelfandTriple.lean`
- **API**
  - `Minlos.GelfandTriple` (data-only)
  - `GelfandTriple.dualEmbedding`
- **Rationale**
  - Provides an abstract interface for Minlos/Gaussian results without committing to a concrete
    `N := 𝓢(E, ℝ)` choice.

### PR F: Import hub (optional)

- **Files**
  - `PhysLean/QFT/Euclidean/Basic.lean`
- **Rationale**
  - Improves ergonomics: downstream code imports one file for the “core Euclidean QFT API”.

## Notes on Mathlib vs PhysLean split

- Anything that is purely about `WeakDual` measurability / measurable spaces is a good **Mathlib PR**
  candidate later (see `docs/mathlib_pr_pipeline.md`).
- The “time direction / spacetime” layer is **PhysLean-shaped**: it is general, but motivated by OS/QFT.

