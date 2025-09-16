import Mathlib
import ym.minkowski.Reconstruction

/-!
Minkowski export smoke test: validate that the OS→Wightman export signature is
available at the interface layer.
-/

namespace YM.Tests

open YM

example : True := by
  -- Check that the export symbol is present (no-op proof)
  have h := YM.Minkowski.wightman_export
  trivial

end YM.Tests
