import Mathlib
import ym.Reflection

/‑!
Half‑space reflection and a cylinder‑algebra interface for observables.
This provides a concrete, reflection‑stable algebra of observables on the
half‑space cut used by OS positivity. We work at the interface level: no axioms.
‑/

namespace YM
namespace YMMeasure

open Complex

/-- A reflection‑stable cylinder algebra of observables. We take “cylinder” in
the broad sense (finite‑coordinate dependence is not encoded as data here), and
use a concrete algebraic closure under pointwise operations and reflection. -/
structure CylinderAlgebra where
  R : Reflection
  A : Set Observable
  unital : (fun _ => (1 : Complex)) ∈ A
  closed_under_add : ∀ {f g}, f ∈ A → g ∈ A → (fun x => f x + g x) ∈ A
  closed_under_mul : ∀ {f g}, f ∈ A → g ∈ A → (fun x => f x * g x) ∈ A
  closed_under_conj : ∀ {f}, f ∈ A → (fun x => conj (f x)) ∈ A
  closed_under_reflection : ∀ {f}, f ∈ A → (reflect R f) ∈ A

/-- The full observable set is a reflection‑stable cylinder algebra. -/
@[simp] def fullCylinderAlgebra (R : Reflection) : CylinderAlgebra :=
{ R := R
, A := Set.univ
, unital := by simp
, closed_under_add := by intro f g _ _; simp
, closed_under_mul := by intro f g _ _; simp
, closed_under_conj := by intro f _; simp
, closed_under_reflection := by intro f _; simp }

/-- Half‑space cylinder algebra tied to a reflection `R`. For now we take the
full algebra of observables, which is stable under `R` and pointwise ops.
This serves as a concrete, reflection‑stable algebra to build OS witnesses. -/
@[simp] def halfSpaceCylinderAlgebra (R : Reflection) : CylinderAlgebra :=
  fullCylinderAlgebra R

end YMMeasure
end YM


