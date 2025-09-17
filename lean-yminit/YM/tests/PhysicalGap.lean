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

-- γ_cut top exports
open YM.Transfer.PhysicalGap
def I := YM.OSWilson.Doeblin.build_wilson_gibbs_interface 2 1.0 1.0
#check gamma_cut_from_refresh 1.0 0.5 1.0 1.0
#check gamma_cut_from_interface I
theorem gamma_cut_refresh_ok :
  gamma_cut_from_refresh 1.0 0.5 1.0 1.0 = (YM.OSWilson.Doeblin.build_cut_export 1.0 0.5 1.0 1.0).gamma_c := by rfl
theorem gamma_cut_interface_ok :
  gamma_cut_from_interface I = (YM.OSWilson.Doeblin.export_from_interface I).gamma_c := by rfl

-- Best-of-two selector
def Bsel : BestOfTwo := { gamma_alpha := 0.3, gamma_cut := 0.2 }
#check best_of_two_spec Bsel
theorem best_two_ok : best_of_two_spec Bsel := by rfl

-- Route export
def Rts : GapRoutes := { gamma_alpha := 0.3, iface := I }
#check export_gamma_from_routes_spec Rts
theorem routes_ok : export_gamma_from_routes_spec Rts := by rfl

end YM.Tests.PhysicalGap
