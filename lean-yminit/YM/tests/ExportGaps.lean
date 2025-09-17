/-!
Examples/tests: instantiate interfaces and export gaps (spec-level).
-/

import YM.OSWilson.Doeblin
import YM.Transfer.PhysicalGap

open YM.OSWilson.Doeblin
open YM.Transfer.PhysicalGap

namespace YM.Tests.ExportGaps

-- Instantiate two example interfaces (stand-in for geometry packs)
def I2 : WilsonGibbsInterface := build_wilson_gibbs_interface 2 1.0 1.0
def I3 : WilsonGibbsInterface := build_wilson_gibbs_interface 3 1.0 1.0

#check export_from_interface_spec I2
#check export_from_interface_spec I3

theorem iface2_ok : export_from_interface_spec I2 := by
  exact export_from_interface_holds I2

theorem iface3_ok : export_from_interface_spec I3 := by
  exact export_from_interface_holds I3

-- Route selection example combining α-route and interface route
def Rsel2 : GapRoutes := { gamma_alpha := 0.25, iface := I2 }
def Rsel3 : GapRoutes := { gamma_alpha := 0.10, iface := I3 }

#check export_gamma_from_routes_spec Rsel2
#check export_gamma_from_routes_spec Rsel3

theorem routes2_ok : export_gamma_from_routes_spec Rsel2 := by rfl
theorem routes3_ok : export_gamma_from_routes_spec Rsel3 := by rfl

end YM.Tests.ExportGaps
