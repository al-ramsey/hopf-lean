import Lake
open Lake DSL

package «hopf_lean» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «HopfLean» {
  -- add any library configuration options here
}
