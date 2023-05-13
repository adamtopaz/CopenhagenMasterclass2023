import Lake
open Lake DSL

package «copenhagenMasterclass2023» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «CopenhagenMasterclass2023» {
  -- add any library configuration options here
}
