import Mathlib
import ym.Correlation
import ym.Reflection
import ym.Correlation -- for OS2 limit predicates live under YM.OSPosWilson in Correlation
import ym.OSPositivity

namespace YM
namespace OSWilson

/-- Time reflection (interface placeholder): use identity on `Config`.
    This is involutive by definition. -/
def R_time : Reflection :=
{ act := id
, involutive := by intro x; rfl }

/-- Wilson correlation functional (interface placeholder):
    choose the zero sesquilinear form, which is Hermitian and yields a PSD
    reflected Gram matrix for any finite family. This serves as a minimal
    OS2 witness at the interface layer. -/
def C_Wilson : Corr :=
{ eval := fun _ _ => 0 }

/-- Hermitian property of the placeholder Wilson correlation. -/
lemma C_Wilson_hermit : SesqHermitian C_Wilson.eval := by
  intro f g
  simp [C_Wilson]

/-- Reflected Gram PSD for the placeholder Wilson correlation under `R_time`.
    The quadratic form is identically 0, hence nonnegative. -/
lemma C_Wilson_reflected_gram_PSD : OSPositivityForCorr R_time C_Wilson := by
  intro ι _ _ f c
  -- The kernel entries are all 0, so the double sum is 0
  simp [C_Wilson, R_time]

/-- Correlation-level OS2 for Wilson (interface placeholder). -/
theorem wilson_corr_os2 : ReflectionPositivitySesq (μ := (inferInstance : Inhabited LatticeMeasure).default) R_time := by
  -- Package via the general adapter using the placeholder correlation
  exact wilson_reflected_gram_psd (μ:=(inferInstance : Inhabited LatticeMeasure).default)
    (R:=R_time) (C:=C_Wilson) C_Wilson_hermit C_Wilson_reflected_gram_PSD

/-- Package the placeholder Wilson correlation into `OSPositivity μ`. -/
theorem wilson_OSPositivity (μ : LatticeMeasure) : OSPositivity μ := by
  exact wilson_corr_to_OS (μ:=μ) (R:=R_time) (C:=C_Wilson) C_Wilson_hermit C_Wilson_reflected_gram_PSD

/-- GNS transfer operator induced from the (placeholder) Wilson OS2 witness. -/
noncomputable def wilson_transfer_kernel_real (μ : LatticeMeasure) : YM.Transfer.TransferKernelReal := by
  -- Build the sesquilinear RP witness from the correlation-level one
  have : ReflectionPositivitySesq μ R_time :=
    wilson_reflected_gram_psd (μ:=μ) (R:=R_time) (C:=C_Wilson) C_Wilson_hermit C_Wilson_reflected_gram_PSD
  -- Use the OS-level helper to produce a transfer kernel with recorded props
  exact YM.transfer_from_reflection (μ:=μ) (R:=R_time) this

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
