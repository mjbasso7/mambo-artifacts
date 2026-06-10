import Lake
open Lake DSL

package "Mambo" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.18.0"

@[default_target]
lean_lib «Mambo» where
  -- Mambo cryptographic construction: Lean 4 formalization
