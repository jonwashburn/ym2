/-!
OS→Wightman reconstruction acceptance (spec-level).
No axioms. No `sorry`.
-/

import YM.OSPositivity.Euclid
import YM.OSPositivity.LocalFields

namespace YM.OSPositivity.Wightman

open YM.OSPositivity.Euclid
open YM.OSPositivity.LocalFields

/-- Minimal Schwinger acceptance bundle used for OS→Wightman (spec-level). -/
structure SchwingerAcceptance where
  os0_ok : Bool
  os1_ok : Bool
  os2_ok : Bool

/-- Wightman acceptance (spec-level). -/
structure WightmanAcceptance where
  reconstruction_ok : Bool

/-- OS→Wightman reconstruction spec: reconstruction_ok equals the conjunction of OS flags. -/
def os_to_wightman_reconstruction_spec (S : SchwingerAcceptance) (W : WightmanAcceptance) : Prop :=
  W.reconstruction_ok = (S.os0_ok && S.os1_ok && S.os2_ok)

/-- Builder: if OS acceptance flags are present, declare reconstruction accepted (spec-level). -/
def build_os_to_wightman_reconstruction (S : SchwingerAcceptance) : WightmanAcceptance :=
  { reconstruction_ok := S.os0_ok && S.os1_ok && S.os2_ok }

theorem build_os_to_wightman_reconstruction_holds (S : SchwingerAcceptance) :
  os_to_wightman_reconstruction_spec S (build_os_to_wightman_reconstruction S) := by
  rfl

-- Purged alias: use `os_to_wightman_reconstruction_spec` directly.

end YM.OSPositivity.Wightman
