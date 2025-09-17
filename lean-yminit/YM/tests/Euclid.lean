/-!
Smoke checks for OS1 equicontinuity/invariance (spec-level).
-/

import YM.OSPositivity.Euclid

open YM.OSPositivity.Euclid

namespace YM.Tests.Euclid

def P : EuclidAggregateParams := { region_size := 1.0, lattice_dim := 4, approx_error := 0.01, tightness := 0.1 }
def O := build_euclid_aggregate P

#check equicontinuity_modulus_spec { region_size := P.region_size } (build_equicontinuity_modulus { region_size := P.region_size })
#check euclid_invariance_limit { rot_ok := true, trans_ok := true }

theorem euclid_aggregate_ok :
  ∃ O : EuclidAggregateOut,
    equicontinuity_modulus_spec { region_size := P.region_size } (build_equicontinuity_modulus { region_size := P.region_size }) ∧
    hypercubic_invariance_spec { lattice_dim := P.lattice_dim } ∧
    rotation_approx_limit_spec { approx_error := P.approx_error } ∧
    translation_limit_spec { tightness := P.tightness } ∧
    euclid_invariance_limit_spec { rot_ok := true, trans_ok := true } := by
  simpa using euclid_aggregate_exists P

theorem euclid_limit_ok : euclid_invariance_limit { rot_ok := true, trans_ok := true } := by
  simpa using euclid_invariance_limit_holds { rot_ok := true, trans_ok := true }

end YM.Tests.Euclid
