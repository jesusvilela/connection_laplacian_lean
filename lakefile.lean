import Lake
open Lake DSL

package connectionLaplacian where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"

@[default_target]
lean_lib ConnectionLaplacian where
  -- expose all files under ConnectionLaplacian/
