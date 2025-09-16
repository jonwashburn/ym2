import Lake
open Lake DSL
package «ym-proof»
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0-rc1"
@[default_target]
lean_lib ym where
  roots := #[`ym]
