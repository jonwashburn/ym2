/-!
Smoke checks for YM.OSWilson.Gibbs (spec-level).
-/

import YM.OSWilson.Gibbs

open YM.OSWilson.Gibbs

namespace YM.Tests.Gibbs

def V  : LatticeVolume := { side := 8 }
def μ  : WilsonGibbs := build_wilson_gibbs V
def V' : LatticeVolume := { side := 4 }
def m  : WilsonGibbs := marginal_to_subvolume μ V'

#check wilson_gibbs_spec μ
#check marginal_to_subvolume_spec μ V' m

theorem gibbs_ok : wilson_gibbs_spec μ := by
  simpa using build_wilson_gibbs_satisfies V

theorem marginal_ok : marginal_to_subvolume_spec μ V' m := by
  simpa using marginal_to_subvolume_satisfies μ V'

-- Inclusion and tightness smoke checks
def incl : VolumeInclusion := { parent := V, sub := V' }
#check consistency_pushforward_spec μ incl m
theorem pushforward_ok : consistency_pushforward_spec μ incl (project_marginal μ incl) := by
  exact consistency_pushforward_holds μ incl

def Rfix : FixedRegion := { radius := 1.0 }
#check tightness_on_fixed_region_spec μ Rfix
theorem tightness_ok : tightness_on_fixed_region_spec μ Rfix := by
  exact tightness_on_fixed_region_holds μ Rfix

end YM.Tests.Gibbs
