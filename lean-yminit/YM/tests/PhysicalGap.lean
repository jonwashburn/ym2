/-!
Quick T15 acceptance smoke checks (compile-time only).
-/

import YM.Transfer.PhysicalGap

open YM.Transfer.PhysicalGap

namespace YM.Tests.PhysicalGap

def P : T15Params :=
  { per := { thetaStar := 0.1, t0 := 1.0, lambda1 := 1.0 }
  , c_cut := 0.2 }

def O : T15Out := build_T15 P

#check T15_accept P O

end YM.Tests.PhysicalGap
