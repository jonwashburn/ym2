/-!
Smoke checks for YM.OSWilson.Cylinder (spec-level).
-/

import YM.OSWilson.Cylinder

open YM.OSWilson.Cylinder

namespace YM.Tests.OScylinder

def H : TimeHalfSpace := build_time_half_space 4
def A : CylinderAlgebra := build_cylinder_algebra H 3
def θ : OSReflection := build_os_reflection

#check cylinder_algebra_spec A
#check reflection_stable_spec A θ

theorem cyl_ok : cylinder_algebra_spec A := by
  simpa using build_cylinder_algebra_satisfies H 3

theorem refl_ok : reflection_stable_spec A θ := by
  have := reflection_stable_holds 4 3
  simpa [H, A, θ] using this

end YM.Tests.OScylinder
