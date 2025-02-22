import Lake
open Lake DSL

package "PlanePartitions" where
  version := v!"0.1.0"

lean_lib «PlanePartitions» where
  -- add library configuration options here

require "leanprover-community" / "mathlib"

@[default_target]
lean_exe "planepartitions" where
  root := `Main
