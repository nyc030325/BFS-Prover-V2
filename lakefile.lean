import Lake
open Lake DSL

package «MiniF2F» {
  -- add any package configuration options here
}


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.10.0"


@[default_target]
lean_lib «Main» {
  -- add any library configuration options here
}

lean_lib «MiniF2F» {
  -- add any library configuration options here
}
