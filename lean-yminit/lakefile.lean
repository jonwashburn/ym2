import Lake
open Lake DSL

package «ym» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0-rc1"

lean_lib «YM» where

@[default_target] lean_exe «ym» where
  root := `Main
