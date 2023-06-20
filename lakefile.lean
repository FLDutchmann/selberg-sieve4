import Lake
open Lake DSL

package selbergSieve {
  -- add package configuration options here
}

lean_lib SelbergSieve {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe selbergSieve {
  root := `Main
}
