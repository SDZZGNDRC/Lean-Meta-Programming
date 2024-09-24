import Lake
open Lake DSL

package «src» where
  -- add package configuration options here

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"

lean_lib «Src» where
--   -- add library configuration options here

@[default_target]
lean_lib «src» where
