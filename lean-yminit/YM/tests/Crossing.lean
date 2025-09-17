/-!
Smoke checks for YM.OSWilson.Crossing (spec-level).
-/

import YM.OSWilson.Crossing

open YM.OSWilson.Crossing

namespace YM.Tests.Crossing

def C2 := build_crossing_kernel_wilson 2

#check hermitian_spec C2
theorem herm_ok : hermitian_spec C2 := by
  simpa using hermitian_holds 2

def G3 := build_reflected_psd_gram 3

#check reflected_psd_gram_spec C2 G3
theorem psd_ok : reflected_psd_gram_spec C2 G3 := by
  have h := reflected_psd_gram_holds 2 3
  simpa [C2, G3] using h

end YM.Tests.Crossing
