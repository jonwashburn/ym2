/-!
Smoke checks for OS positivity export (spec-level).
-/

import YM.OSPositivity.OS2

open YM.OSPositivity.OS2

namespace YM.Tests.OS2

def W := build_os_positivity_from_crossing 4 3 5

#check os_positivity_spec W

theorem os2_ok : os_positivity_spec W := by
  simpa [W] using build_os_positivity_from_crossing_holds 4 3 5

#check os_positivity_spec W
theorem os2_alias_ok : os_positivity_spec W := by
  simpa [W] using build_os_positivity_from_crossing_holds 4 3 5

end YM.Tests.OS2
