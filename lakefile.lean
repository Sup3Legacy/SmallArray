import Lake
open Lake DSL

package «SmallArray» {
  -- add package configuration options here
}

lean_lib «SmallArray» {
  -- add library configuration options here
}

require std from git "https://github.com/leanprover/std4.git" @ "main"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
