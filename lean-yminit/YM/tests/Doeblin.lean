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

-- Wilson kernel derivation and domination acceptance
def B2 := build_wilson_boundary_weight 2
#check derived_from_gibbs_spec 2 B2 (normalize_to_inter_slab 2 B2)
theorem derived_ok : derived_from_gibbs_spec 2 B2 (normalize_to_inter_slab 2 B2) := by
  exact derived_from_gibbs_holds 2 B2

def I2 : WilsonGibbsInterface := build_wilson_gibbs_interface 2 1.0 1.0
#check export_from_interface_spec I2
theorem export_ok : export_from_interface_spec I2 := by
  exact export_from_interface_holds I2

end YM.Tests.Doeblin
