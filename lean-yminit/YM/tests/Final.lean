/-!
Smoke checks for the Clay final theorem acceptance (spec-level).
-/

import YM.Clay.Final

open YM.Clay.Final

namespace YM.Tests.Final

def P : FinalParams := { doeblin := { kappa0 := 0.5, t0 := 1.0, lambda1 := 1.0, S0 := 0.1, a := 1.0 } }
def A := build_final P

#check final_clay_spec P A

theorem final_ok : final_clay_spec P A := by
  simpa using build_final_holds P

end YM.Tests.Final
