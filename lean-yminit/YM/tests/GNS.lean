/-!
Smoke checks for GNS and transfer (spec-level).
-/

import YM.OSPositivity.GNS

open YM.OSPositivity.GNS

namespace YM.Tests.GNS

def P := build_gns_transfer_pack 4 3 5

#check gns_transfer_pack_spec P

theorem gns_pack_ok : gns_transfer_pack_spec P := by
  simpa [P] using build_gns_transfer_pack_holds 4 3 5

end YM.Tests.GNS
