# Mathlib PR pipeline (from `OSforGFF/`)

This document is a **staging note** for extracting Mathlib-eligible results from this workspace.
It is intentionally written in “PR-sized chunks”, with each chunk aiming for:

- minimal imports
- no project-specific definitions
- Mathlib naming/placement conventions
- `#lint`-clean code

## Snapshot: what is already “pure Mathlib” in this workspace?

The following modules (in `OSforGFF/`) appear to be **standalone extensions of Mathlib** (i.e. they import only Mathlib, or can be made to do so with small edits):

- `OSforGFF/WeakDualMeasurability.lean`
- `OSforGFF/FourierTransforms.lean`
- `OSforGFF/LaplaceIntegral.lean`
- `OSforGFF/Analysis/Distribution/Sobolev.lean` (compat layer, likely Mathlib-adjacent)
- `OSforGFF/FunctionalAnalysis.lean` (large; should be split before upstreaming)

Other files like `OSforGFF/SchurProduct.lean`, `OSforGFF/HadamardExp.lean`, and `OSforGFF/GaussianRBF.lean` *may* overlap with existing Mathlib results; they should be upstreamed only after confirming novelty (or rephrased as missing lemma patches).

## Proposed PR sequence (high confidence → lower confidence)

### PR 1: Weak-* dual measurability lemmas (very small)

- **Source**: `OSforGFF/WeakDualMeasurability.lean`
- **What**:
  - measurability of evaluation maps `ω ↦ ω f` on `WeakDual 𝕜 E`
  - coordinatewise measurability into a Pi-type (the coercion `ω ↦ (fun f => ω f)`)
- **Suggested Mathlib destination**:
  - `Mathlib/Topology/Algebra/Module/WeakDual/Measurability.lean` (or nearby in the `WeakDual` folder)
- **Suggested naming**:
  - `WeakDual.measurable_eval` / `WeakDual.aemeasurable_eval`
  - `WeakDual.measurable_coeFun` / `WeakDual.aemeasurable_coeFun`
- **Notes**:
  - This file should not live in a project namespace for upstreaming; it should be `namespace WeakDual` directly.

### PR 2: Laplace integral identity for \(K_{1/2}\) (self-contained, but math-heavy)

- **Source**: `OSforGFF/LaplaceIntegral.lean`
- **What**:
  - identity of the form `∫₀^∞ s^{-1/2} exp(-a/s - b*s) ds = √(π/b) * exp(-2√(ab))`
  - plus intermediate lemmas (Glasser / Cauchy–Schlömilch type identity)
- **Suggested Mathlib destination**:
  - likely within `Mathlib/Analysis/SpecialFunctions/Integrals.lean`-adjacent area
  - or a dedicated file like `Mathlib/Analysis/SpecialFunctions/LaplaceIntegral.lean` if it’s substantial
- **Risk / diligence**:
  - confirm Mathlib doesn’t already have this exact lemma (or a more general Bessel-K identity)
  - if it exists, convert this into a “missing simp/bridge lemma” PR instead of new theory

### PR 3: Fourier-transform identities used in QFT reflection positivity (medium)

- **Source**: `OSforGFF/FourierTransforms.lean`
- **What**:
  - 1D transform pair between Lorentzian `1/(k^2+μ^2)` and `exp(-μ|x|)`
  - measure-preserving/measurable-equivalence rearrangements for triple integrals (useful generally)
- **Suggested Mathlib destination**:
  - either `Mathlib/Analysis/Fourier/` (if phrased in Mathlib’s conventions)
  - or `Mathlib/MeasureTheory/Integral/Prod`-adjacent (for the measure-preserving reorder equivalences)
- **Risk / diligence**:
  - normalization conventions differ (physics vs Mathlib). For upstreaming, statements should be in Mathlib’s convention, with “physics convention” as corollaries if needed.

### PR 4: Sobolev/Bessel-potential compat layer (medium, depends on Mathlib direction)

- **Source**: `OSforGFF/Analysis/Distribution/Sobolev.lean`
- **What**:
  - a `fourierMultiplierCLM` compat API for tempered distributions
  - lemmas relating Laplacian/derivatives to Fourier multipliers
- **Suggested Mathlib destination**:
  - near `Mathlib/Analysis/Distribution/` and `Mathlib/Analysis/Fourier/` distribution infrastructure
- **Risk / diligence**:
  - check whether Mathlib maintainers prefer such API in Mathlib core vs in an applications repo

### PR 5: “Functional analysis utilities” split into upstreamable micro-PRs (large)

- **Source**: `OSforGFF/FunctionalAnalysis.lean`
- **Approach**:
  - split into 5–10 files, each with a narrow theme (Schwartz/integrability, Lp embeddings, etc.)
  - upstream only the parts that are clearly general and not tied to `OSforGFF.Basic`-level definitions
- **Why staged**:
  - the file is large and mixes many topics; upstreaming should minimize review load.

## Non-goals for Mathlib extraction (should stay downstream)

- OS axiom definitions and QFT-specific structures (`OSforGFF/OS_Axioms.lean`, `OS*_GFF.lean`, `GFFmaster*.lean`)
- the GFF measure construction pipeline and its packaging (`OSforGFF/Minlos*`, `OSforGFF/GFF/*`)
- spacetime/time-direction infrastructure that is tailored to this project’s notion of test functions (`OSforGFF/Spacetime/*`)

