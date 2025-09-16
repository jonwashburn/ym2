import Lake
open Lake DSL

package «ym» where

lean_lib «YM» where

@[default_target] lean_exe «ym» where
  root := `Main
