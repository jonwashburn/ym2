/-!
Quick T11 acceptance smoke checks (compile-time only).
-/

import YM.OSWilson.OddConeDeficit

open YM.OSWilson.OddConeDeficit

namespace YM.Tests.OddCone

def P : T11Params :=
  { gram := { A := 1.0, mu := 0.5, Cg := 10.0, nu := 0.7 }
  , mix  := { B := 0.2, nu' := 1.0 }
  , diag := { rho := 0.8 }
  , stepA := 1.0 }

def O : T11Out := build_T11 P

#check T11_accept P O

end YM.Tests.OddCone
