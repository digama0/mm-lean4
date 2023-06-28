import Lake
open Lake DSL

package «mm-lean4»

require std from git "https://github.com/leanprover/std4" @ "main"

@[default_target]
lean_lib Metamath

@[default_target]
lean_exe «mm-lean4» where
  root := `Metamath
