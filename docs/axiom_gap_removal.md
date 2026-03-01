# Axiom/sorry gap removal plan (tracked repos)

This document records the remaining **semantic gaps** in upstream/snapshot repos that live in the
workspace, and the strategy to remove or isolate them without polluting the proved `OSforGFF`
surface.

## gaussian-field (`gaussian-field-main/`)

### Current gaps

- **Active Lean axioms** (must be proved or isolated upstream):
  - `gaussian-field-main/HeatKernel/PositionKernel.lean`:
    - `mehlerKernel_eq_series`
    - `circleHeatKernel_pos`

### Short-term isolation (already applied in `OSforGFF`)

- `OSforGFF` does not vendor `gaussian-field-main/` as `lean_lib`s.
- The only direct reference point is `OSforGFF/GFF/Adapter/GaussianField.lean`, which is kept as an
  adapter module and should remain **non-default** (i.e. not imported by the main entrypoints).

### Upstream remediation options

- **Option 1 (preferred)**: prove the two axioms in `HeatKernel/PositionKernel.lean`.
  - If the proofs require missing Mathlib lemmas, upstream those first (Mathlib PR track).
- **Option 2**: replace `axiom` with explicit hypotheses:

  - define a structure encapsulating the needed heat-kernel facts;
  - state theorems as `theorem ... (h : HeatKernelFacts ...) : ...` so downstream projects remain
    axiom-free.

## OS reconstruction (`OSreconstruction-1-main/`)

### Current gaps

- Toolchain and dependency mismatch:
  - Lean toolchain differs from `OSforGFF` (uses `v4.27.0-rc1`)
  - Mathlib on `master`
- Critical axioms (named):
  - `OSreconstruction-1-main/OSReconstruction/Wightman/Reconstruction/AnalyticContinuation.lean`:
    - `edge_of_the_wedge`
    - `bargmann_hall_wightman`
- Many `sorry`s (research track).

### Strategy

- Keep `OSreconstruction-1-main/` as a **separate package** until axioms/sorries are addressed.
- Share only **definitions/interfaces**, not theorem-level dependencies, to avoid importing semantic
  gaps into the proved GFF pipeline.

