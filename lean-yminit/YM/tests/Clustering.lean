/-!
Smoke checks for OS3 clustering acceptance (spec-level).
-/

import YM.OSPositivity.Clustering
import YM.Transfer.PhysicalGap

open YM.OSPositivity.Clustering
open YM.Transfer.PhysicalGap

namespace YM.Tests.Clustering

def G := build_gap_from_doeblin { kappa0 := 0.5, t0 := 1.0, lambda1 := 1.0, S0 := 0.1, a := 1.0 }
def A := build_clustering_from_doeblin G 1.0

#check clustering_spec { gamma_phys := G.gamma_phys, region_size := 1.0 } A

theorem clustering_ok : clustering_spec { gamma_phys := G.gamma_phys, region_size := 1.0 } A := by
  simpa using build_clustering_from_doeblin_holds G 1.0

end YM.Tests.Clustering
