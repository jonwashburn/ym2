import Mathlib
import Mathlib.Algebra.BigOperators.Basic
import ym.Reflection

/-!
YM correlation interface: abstract correlation functional and OS positivity schema
linked to positive semidefiniteness of Gram matrices under reflection.
-/

namespace YM

open scoped BigOperators

/-- Abstract correlation functional. -/
structure Corr where
  eval : Observable → Observable → Complex

/--
OS-positivity schema for the correlation functional under reflection `R`:
for every finite family of observables and coefficients, the reflected two-point
form yields a nonnegative quadratic form.
-/
def OSPositivityForCorr (R : Reflection) (C : Corr) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → Observable) (c : ι → Complex),
      0 ≤ (∑ i, ∑ j,
        star (c i) * C.eval (f i) (reflect R (f j)) * (c j)).re

/-- Adapter: OS-positivity for the correlation functional yields a
positive semidefinite Gram matrix for finite families of observables. -/
theorem gram_pos_of_OS_corr
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Reflection} {C : Corr}
    (h : OSPositivityForCorr R C)
    (f : ι → Observable) :
    PosSemidefKernel (fun i j => C.eval (f i) (reflect R (f j))) := by
  intro v
  simpa using (h (ι := ι) f v)

/-- Adapter toward Agent 1: correlation-level OS positivity implies the
sesquilinear reflection-positivity interface.
-/
theorem rp_sesq_of_OS_corr
    {μ : LatticeMeasure} {R : Reflection} {C : Corr}
    (hHerm : SesqHermitian C.eval)
    (h : OSPositivityForCorr R C) : ReflectionPositivitySesq μ R := by
  refine ⟨C.eval, hHerm, ?_⟩
  intro ι _ _ f
  exact gram_pos_of_OS_corr (ι := ι) (R := R) (C := C) h f

/-- Bridge alias: correlation-level OS positivity implies sesquilinear
reflection positivity using `S := C.eval`. -/
theorem RP_sesq_of_corr_OS
    {μ : LatticeMeasure} {R : Reflection} {C : Corr}
    (hHerm : SesqHermitian C.eval)
    (h : OSPositivityForCorr R C) : ReflectionPositivitySesq μ R :=
  rp_sesq_of_OS_corr (μ := μ) (R := R) (C := C) hHerm h

end YM
