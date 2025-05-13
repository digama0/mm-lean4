import Lake
open Lake DSL

package «mm-lean4»

@[default_target]
lean_lib Metamath where
  roots := #[`Metamath.Verify]

@[default_target]
lean_lib MetamathExperimental where
  roots := #[`Metamath.Translate]

@[default_target]
lean_exe «mm-lean4» where
  root := `Metamath
