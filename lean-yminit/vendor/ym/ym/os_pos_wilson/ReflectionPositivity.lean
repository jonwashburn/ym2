import Mathlib
import ym.Correlation
import ym.Reflection
import ym.Correlation -- for OS2 limit predicates live under YM.OSPosWilson in Correlation

namespace YM
namespace OSWilson

/-- Correlation-level OS positivity ⇒ sesquilinear reflection positivity (alias).
This re-exports the general adapter for convenience in the Wilson namespace. -/
theorem wilson_reflected_gram_psd
  {μ : LatticeMeasure} {R : Reflection} {C : Corr}
  (hHerm : SesqHermitian C.eval)
  (h : OSPositivityForCorr R C) : ReflectionPositivitySesq μ R :=
  YM.rp_sesq_of_OS_corr (μ := μ) (R := R) (C := C) hHerm h

/-- Backward-compatibility stub kept for callers written against `True`. -/
theorem reflection_positivity_stub : True := by trivial

end OSWilson
end YM
