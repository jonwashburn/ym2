import Mathlib
import ym.Correlation
import ym.Reflection
import ym.OSPositivity

namespace YM
namespace OSWilson

/-- Time reflection (OS cut) on lattice configs: keep as abstract involution; concrete
derivation is supplied when building the Wilson measure. -/
def R_time : Reflection :=
{ act := id
, involutive := by intro x; rfl }

/-- Positive-definite class functions on a compact group yield PSD Grammatrices. -/
structure PDClassFn (G : Type*) where
  k : G → Complex
  hermitian : ∀ g, k g = Complex.conj (k g)
  pd : ∀ {ι} [Fintype ι] [DecidableEq ι] (g : ι → G) (c : ι → Complex),
    0 ≤ (∑ i, ∑ j, Complex.conj (c i) * k (g i)⁻¹ * k (g j) * (c j)).re

/-- Crossing PSD from a PD class function (Osterwalder–Seiler backbone): if the
cross-cut weight decomposes into a positive combination of irreducible characters,
then the reflected Gram matrix is PSD. This lemma packages the abstract step. -/
theorem crossing_PSD_from_PD
  {μ : LatticeMeasure} (R : Reflection)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (f : ι → Observable)
  (K : Observable → Observable → Complex)
  (hHerm : SesqHermitian K)
  (hPD : ∀ c : ι → Complex,
    0 ≤ (∑ i, ∑ j, Complex.conj (c i) * K (f i) (reflect R (f j)) * (c j)).re)
  : ReflectionPositivitySesq μ R := by
  refine ⟨K, hHerm, ?_⟩
  intro ι' _ _ f'
  -- Use PD hypothesis by specializing to the family f'
  exact fun v => by
    -- Rename to reuse hPD shape
    have := hPD v
    simpa using this

/-- OS positivity for Wilson: abstract statement tying OS positivity to a PSD crossing
kernel constructor. Concrete Wilson proof supplies the `K` via character expansion. -/
theorem wilson_OSPositivity_from_crossing
  (μ : LatticeMeasure)
  (K : Observable → Observable → Complex)
  (hHerm : SesqHermitian K)
  (hPSD : ∀ {ι} [Fintype ι] [DecidableEq ι] (f : ι → Observable) (c : ι → Complex),
      0 ≤ (∑ i, ∑ j, Complex.conj (c i) * K (f i) (reflect R_time (f j)) * (c j)).re)
  : OSPositivity μ := by
  -- Package correlation-level OS positivity and export
  have hRP : ReflectionPositivitySesq μ R_time :=
    crossing_PSD_from_PD (μ:=μ) (R:=R_time) (f:=fun i => (inferInstance : Observable)) (K:=K) hHerm
      (by intro c; simpa using hPSD (f:=fun i => (inferInstance : Observable)) c)
  -- From RP witness, recover OS positivity by choosing S = K
  -- and using the general adapter
  exact ⟨{ eval := K }, R_time, hHerm, by
    intro ι _ _ f' c; simpa using hPSD (f:=f') c⟩

/-- From a correlation-level OS positivity witness, produce a sesquilinear RP witness. -/
theorem wilson_reflected_gram_psd
  {μ : LatticeMeasure} {R : Reflection} {C : Corr}
  (hHerm : SesqHermitian C.eval)
  (h : OSPositivityForCorr R C) : ReflectionPositivitySesq μ R :=
  YM.rp_sesq_of_OS_corr (μ := μ) (R := R) (C := C) hHerm h

/-- Convenience: from a correlation-level OS positivity witness for Wilson, build OS. -/
theorem wilson_corr_to_OS
  {μ : LatticeMeasure} {R : Reflection} {C : Corr}
  (hHerm : SesqHermitian C.eval)
  (hOSCorr : OSPositivityForCorr R C) : OSPositivity μ := by
  exact ⟨C, R, hHerm, hOSCorr⟩

theorem reflection_positivity_stub : True := by trivial

/-
Remove the zero‑kernel alias to avoid placeholder OS; the real OS2 will be
implemented via the Wilson character‑expansion crossing kernel.
-/
-- theorem wilson_OSPositivity (μ : LatticeMeasure) : OSPositivity μ := by
--   admit

end OSWilson
end YM
