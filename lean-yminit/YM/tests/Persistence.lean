/-!
Smoke checks for spectral persistence (spec-level).
-/

import YM.SpectralStability.Persistence
import YM.Transfer.PhysicalGap

open YM.SpectralStability.Persistence
open YM.Transfer.PhysicalGap

namespace YM.Tests.Persistence

def G := build_gap_from_doeblin { kappa0 := 0.5, t0 := 1.0, lambda1 := 1.0, S0 := 0.1, a := 1.0 }
def A := build_riesz_from_gap G

#check riesz_semicontinuity_spec { gamma_phys := G.gamma_phys } A

theorem persistence_ok : riesz_semicontinuity_spec { gamma_phys := G.gamma_phys } A := by
  simpa using build_riesz_from_gap_holds G

end YM.Tests.Persistence
