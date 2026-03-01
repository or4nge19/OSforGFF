## `Common/Mathlib` upstream queue

`Common/Mathlib` is treated as a **temporary Mathlib patch queue**: files here are either intended
to become Mathlib PRs, or are local glue/docs that should disappear once upstreaming is complete.

### Category A: upstream-to-Mathlib PR candidates (core math content)

These should be split into a small number of focused Mathlib PRs (grouped by dependency):

- `Common/Mathlib/MeasureTheory/ParametricDominatedConvergence.lean`
- `Common/Mathlib/Probability/Distributions/Gaussian/`
  - `CameronMartinThm.lean`
  - `CameronMartin.lean`
  - `CameronMartinTilt.lean`
  - `TiltKernel.lean`
  - `CameronMartinFernique.lean`
  - `SubGaussian.lean`
  - `CameronMartinRV.lean`
  - `CameronMartinIBP.lean`
  - `CameronMartinIBPDeriv.lean`
  - `CameronMartinIBPAnalytic.lean`
  - `IntegrationByParts.lean`
  - `Real.lean`
- `Common/Mathlib/Probability/Distributions/Gaussian_IBP_Hilbert.lean`
- `Common/Mathlib/Probability/Distributions/GaussianIntegrationByParts.lean`

### Category B: local staging / API reshaping (should shrink over time)

These are useful while upstreaming is in progress, but should not become long-term dependencies:

- `Common/Mathlib/Probability/Distributions/Gaussian_IBP_HilbertAPI.lean`
- `Common/Mathlib/Probability/Distributions/Gaussian/CameronMartinAPI.lean`
- `Common/Mathlib/Probability/Distributions/Gaussian/CompletionResultsToBeMoved.lean`

### Category C: local documentation (never upstream verbatim)

- `Common/Mathlib/Probability/Distributions/Gaussian/MathlibDocumentationStyle.md`
- `Common/Mathlib/Probability/Distributions/Gaussian/MathlibNamingConventions.md`
- `Common/Mathlib/Probability/Distributions/Gaussian/MathlibStyle.md`

### Deprecation/removal plan (once PRs land)

- **Step 1**: Replace any imports of `Common/Mathlib/...` in non-`Common/` packages with the new
  Mathlib imports (or PhysLean “front door” re-export modules, if introduced).
- **Step 2**: Delete Category B staging modules once all downstream code has migrated.
- **Step 3**: Delete Category A `.lean` files from `Common/` once fully upstreamed and the repo’s
  Mathlib pin includes the merged PRs.

