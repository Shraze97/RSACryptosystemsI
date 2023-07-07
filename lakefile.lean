import Lake
open Lake DSL

package «rSACryptosystemsI» {
  -- add package configuration options here
  precompileModules := true
}

@[default_target]
lean_lib «RSACryptosystemsI» {
  -- add library configuration options here
}
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «rSACryptosystemsI» {
  root := `Main
  supportInterpreter := true
}
