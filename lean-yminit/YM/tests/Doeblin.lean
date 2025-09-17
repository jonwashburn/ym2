/-!
Quick smoke checks for YM.OSWilson.Doeblin domination/cut export stubs.
These are compile-time checks only (no runtime assertions).
-/

import YM.OSWilson.Doeblin

open YM.OSWilson.Doeblin

namespace YM.Tests.Doeblin

-- SU(2) proxy: small nCells
#check build_haar_domination_uniform
#check build_domination_cut

def P2 : DominationCutParams := { nCells := 2, a := 1.0, lambda1 := 1.0 }
def O2 : DominationCutOut := build_domination_cut P2

#check domination_cut_spec P2 O2

-- SU(3) proxy: slightly larger nCells
def P3 : DominationCutParams := { nCells := 3, a := 1.0, lambda1 := 1.5 }
def O3 : DominationCutOut := build_domination_cut P3

#check domination_cut_spec P3 O3

end YM.Tests.Doeblin
