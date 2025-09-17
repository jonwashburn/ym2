/-!
Smoke checks for OS→Wightman reconstruction acceptance (spec-level).
-/

import YM.OSPositivity.Wightman

open YM.OSPositivity.Wightman

namespace YM.Tests.Wightman

def S : SchwingerAcceptance := { os0_ok := true, os1_ok := true, os2_ok := true }
def W : WightmanAcceptance := build_os_to_wightman_reconstruction S

#check os_to_wightman_reconstruction_spec S W

theorem wightman_ok : os_to_wightman_reconstruction_spec S W := by
  simpa using build_os_to_wightman_reconstruction_holds S

end YM.Tests.Wightman
