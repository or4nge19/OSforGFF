# Consolidation notes (workspace hygiene)

The `OSforGFF` package is intended to build as a **standalone** Lake package.
This workspace also contains other Lean projects (snapshots / upstream checkouts), but they are not
vendored into `OSforGFF` as extra `lean_lib`s.

## What changed

- `lakefile.lean` no longer mounts `gaussian-field-main/` or `PhysLean-master/` as extra `lean_lib`s.
- `.gitignore` excludes snapshot repos (including `GFF4D-main/`, `GFF-main/`, `QFTFramework-main/`,
  `gaussian-field-main/`, `PhysLean-master/`, `OSreconstruction-1-main/`) from the main repo history.

## Build expectations

- **Main package**: from repo root, `lake build` (this should succeed).
- **Snapshot repos**: build from within each repo directory if you want to work on them. They may:
  - have different Mathlib pins,
  - have `sorry`/`axiom`s,
  - use different Lean toolchains (notably `OSreconstruction-1-main/`).

## Archived/superseded code

- `GFF4D-main/` is treated as a superseded snapshot (kept for reference only). It is intentionally
  excluded from the main build and from version control of the proved development.

