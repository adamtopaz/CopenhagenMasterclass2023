import Lake
open Lake DSL

package «copenhagenMasterclass2023» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require find_with_gpt from git
  "https://github.com/adamtopaz/find_with_gpt.git"

@[default_target]
lean_lib «CopenhagenMasterclass2023» {
  globs := #[
    .andSubmodules `TopCat,
    .andSubmodules `Condensed, 
    .andSubmodules `Profinite,
    .andSubmodules `ExtrDisc,
    .andSubmodules `CompHaus,
    .andSubmodules `AddCommGroup
    ]
  -- add any library configuration options here
}

/-
lean_lib «Condensed» where
  roots := #[`Condensed]

lean_lib «Profinite» where
  roots := #[`Profinite]

lean_lib «ExtrDisc» where
  roots := #[`ExtrDisc]

lean_lib «CompHaus» where
  roots := #[`CompHaus]
-/