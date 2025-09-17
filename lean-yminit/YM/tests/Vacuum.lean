/-!
Smoke checks for OS4–OS5 unique vacuum and open gap export (spec-level).
-/

import YM.OSPositivity.Vacuum

open YM.OSPositivity.Vacuum

namespace YM.Tests.Vacuum

def dg : YM.Transfer.PhysicalGap.GapFromDoeblinParams :=
  { kappa0 := 0.5, t0 := 1.0, lambda1 := 1.0, S0 := 0.1, a := 1.0 }

def X := build_vacuum_gap_export 4 3 5 dg

#check vacuum_gap_export_spec 4 3 5 dg X

theorem vac_gap_ok : vacuum_gap_export_spec 4 3 5 dg X := by
  simpa using build_vacuum_gap_export_holds 4 3 5 dg

end YM.Tests.Vacuum
