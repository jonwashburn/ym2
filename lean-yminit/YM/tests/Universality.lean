/-!
Smoke checks for universality (spec-level).
-/

import YM.SpectralStability.Universality

open YM.SpectralStability.Universality

namespace YM.Tests.Universality

def C : CrossRegParams := { delta := 0.01 }
def A := build_cross_regularization C
#check cross_regularization_spec C A
theorem crossreg_ok : cross_regularization_spec C A := by
  simpa using build_cross_regularization_holds C

def G : GapUniversalityParams := { gamma1 := 1.0, gamma2 := 1.0 }
def U := build_gap_universality G
#check gap_universality_spec G U
theorem gapuni_ok : gap_universality_spec G U := by
  simpa using build_gap_universality_holds G

end YM.Tests.Universality
