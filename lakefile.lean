import Lake
open Lake DSL

package «OSforGFF» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

require PhysLean from "./PhysLean-master"


lean_lib KolmogorovExtension4 where
  srcDir := "."

lean_lib BrownianMotion where
  srcDir := "."

lean_lib Pphi2 where

lean_lib StochasticPDE where

lean_lib Common where

-- Note: this workspace contains other Lean projects (e.g. `PhysLean-master/`,
-- `gaussian-field-main/`, `QFTFramework-main/`, …), but `OSforGFF` intentionally does *not*
-- vendor them as extra `lean_lib`s. Build those projects in their own directories, or add them
-- as explicit `require` dependencies in a dedicated adapter package if needed.

@[default_target]
lean_lib «OSforGFF» where
  -- add any library configuration options here

lean_lib «DependencyExtractor» where
  -- Dependency extraction metaprogram
