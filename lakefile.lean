import Lake
open Lake DSL

package "spamegg1-lean" where
  version := v!"0.1.0"

lean_lib «Spamegg1Lean» where
  -- add library configuration options here

@[default_target]
lean_exe "spamegg1-lean" where
  root := `Main

-- @[lint_driver]
-- lean_exe ???

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
-- require mathlib from git "https://github.com/leanprover-community/mathlib4"
