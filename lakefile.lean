import Lake
open Lake DSL

package "spamegg1-lean" where
  version := v!"0.1.0"

lean_lib «Spamegg1Lean» where
  -- add library configuration options here

@[default_target]
lean_exe "spamegg1-lean" where
  root := `Main
