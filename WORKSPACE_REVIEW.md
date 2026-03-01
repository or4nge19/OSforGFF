# Workspace review (for multi-stage Mathlib + PhysLean PR pipeline)

This workspace contains multiple Lean projects (some proved, some snapshot/vendor copies, some actively sorry’d research branches).
The goal of consolidation is to ensure **the proved PR surface** is:

- **toolchain-pinned**
- **dependency-pinned**
- **sorry/axiom/admit-free**
- **idiomatic (Mathlib + PhysLean)**
- and that other repos are clearly **separate packages** (not “mounted” as extra `lean_lib`s inside the proved package).

## Repository classification (current state)

| Directory | Package name | Lean toolchain | Dependencies pinned? | `sorry` | Lean `axiom` | Recommended role |
|---|---|---:|---:|---:|---:|---|
| `./` | `OSforGFF` | `v4.28.0` | Mathlib `v4.28.0` | **0** (in `OSforGFF/`) | **0** (in `OSforGFF/`) | **Primary upstream target** (Mathlib-extract + PhysLean-facing bridge) |
| `gaussian-field-main/` | `GaussianField` | `v4.28.0` | **No** (mathlib rev not pinned in `lakefile.lean`) | mostly docs | **2 active axioms** (`HeatKernel/PositionKernel.lean`) | **Separate dependency repo**; do not depend on its axioms in proved surface |
| `PhysLean-master/` | `PhysLean` | `v4.28.0` | Mathlib `v4.28.0` | many (tracked via `@[sorryful]`) | 1 meta axiom (`PhysLean/Meta/Informal/SemiFormal.lean`) | **Upstream project**; keep separate; don’t vendor into proved `OSforGFF` |
| `QFTFramework-main/` | `QFTFramework` | `v4.28.0` | pinned commit | very few | **many axioms** (notably `Spacetime/Torus.lean`) | **Separate framework repo**; acceptable axiomatizations if explicitly scoped |
| `GFF-main/` | `GFF` | `v4.28.0` | depends on git `main` branches | many | ≥1 | **Historical/bridge demo**; should not be used as correctness evidence |
| `GFF4D-main/` | `OSforGFF` (older snapshot) | `v4.28.0` | older Mathlib commit | some | some | **Superseded snapshot**; should be excluded/archived (avoid confusion) |
| `OSreconstruction-1-main/` | `OSReconstruction` | `v4.27.0-rc1` | Mathlib `master` | many (critical path) | **2 named axioms** (analytic continuation) | **Separate research track**; keep decoupled from proved GFF pipeline |

Notes:

- Counts above refer to **actual Lean keywords** in each repo (not informal docs), but many repos also contain TODO/planning documentation that mentions “axiom/sorry” as text.
- In `OSforGFF/`, `sorry`/`axiom`/`admit` are absent in the proved library itself; this is the key asset to preserve for PR readiness.

## Immediate consolidation decisions (actionable)

### 1) Make the proved surface self-contained

- The root `lakefile.lean` currently “mounts” vendored repos by declaring them as extra `lean_lib`s with `srcDir := "…-main"` (e.g. `PhysLean-master`, `gaussian-field-main`).
- Consolidation target: **remove those `lean_lib` mounts** and treat those directories as **separate Lake packages** (or git dependencies) instead.

### 2) Keep axioms/sorries quarantined

- `OSforGFF` should not import from `gaussian-field-main` *unless* explicitly through an adapter module that is **not part of the default build**.
- `OSreconstruction-1-main` should remain a separate package until its critical-path sorries and the two named axioms are resolved or converted into explicit hypotheses.

### 3) Prepare PR tracks

- **Mathlib track**: extract general-purpose results from `OSforGFF/` (Fourier/Parseval, positive-definite kernels, weak-* measurability glue, etc.) into small, theme-based PRs.
- **PhysLean track**: provide a minimal, idiomatic interface layer that downstream libraries can instantiate without importing all of `OSforGFF`.

## How to build (after consolidation)

- **Main proved package**: from workspace root run `lake build` (default target `OSforGFF`).
- **Other repos**: build in their own directory (`gaussian-field-main`, `PhysLean-master`, `QFTFramework-main`, `OSreconstruction-1-main`) so their placeholder status does not pollute the proved package.

