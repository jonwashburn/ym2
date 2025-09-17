import Mathlib
import ym.Correlation
import ym.Reflection
import ym.Correlation -- for OS2 limit predicates live under YM.OSPosWilson in Correlation
import ym.OSPositivity

namespace YM
namespace OSWilson

/-- Correlation-level OS positivity ⇒ sesquilinear reflection positivity (alias).
This re-exports the general adapter for convenience in the Wilson namespace. -/
theorem wilson_reflected_gram_psd
  {μ : LatticeMeasure} {R : Reflection} {C : Corr}
  (hHerm : SesqHermitian C.eval)
  (h : OSPositivityForCorr R C) : ReflectionPositivitySesq μ R :=
  YM.rp_sesq_of_OS_corr (μ := μ) (R := R) (C := C) hHerm h

/-- Convenience: from a correlation-level OS positivity witness for Wilson
    (Hermitian `C` and reflected Gram PSD), build the interface `OSPositivity μ`.
    This packages `(R, C)` for downstream use (e.g. GNS transfer construction). -/
theorem wilson_corr_to_OS
  {μ : LatticeMeasure} {R : Reflection} {C : Corr}
  (hHerm : SesqHermitian C.eval)
  (hOSCorr : OSPositivityForCorr R C) : OSPositivity μ := by
  exact ⟨C, R, hHerm, hOSCorr⟩

/-- Backward-compatibility stub kept for callers written against `True`. -/
theorem reflection_positivity_stub : True := by trivial

end OSWilson
end YM
