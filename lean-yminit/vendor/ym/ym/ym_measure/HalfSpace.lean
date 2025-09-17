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

/-- Half-space projection data: a projection π commuting with reflection R. -/
structure HalfSpaceProj where
  R : Reflection
  π : Config → Config
  idempotent : ∀ x, π (π x) = π x
  commutes : ∀ x, π (R.act x) = R.act (π x)

/-- Observables that depend only on the projected (time ≥ 0) coordinates. -/
def dependsOn (π : Config → Config) (f : Observable) : Prop := ∀ x, f x = f (π x)

/-- Build a reflection-stable cylinder algebra from a commuting projection. -/
def halfSpaceCylinderAlgebraOf (H : HalfSpaceProj) : CylinderAlgebra :=
{ R := H.R
, A := { f | dependsOn H.π f }
, unital := by
    intro x; rfl
, closed_under_add := by
    intro f g hf hg x; dsimp [dependsOn] at hf hg ⊢;
    simp [hf x, hg x]
, closed_under_mul := by
    intro f g hf hg x; dsimp [dependsOn] at hf hg ⊢;
    simp [hf x, hg x]
, closed_under_conj := by
    intro f hf x; dsimp [dependsOn] at hf ⊢;
    simp [hf x]
, closed_under_reflection := by
    intro f hf x; dsimp [dependsOn] at hf ⊢;
    -- (reflect R f) x = f (R x) = f (π (R x)) = f (R (π x)) = (reflect R f) (π x)
    calc
      (reflect H.R f) x = f (H.R.act x) := rfl
      _ = f (H.π (H.R.act x)) := by simpa using hf (H.R.act x)
      _ = f (H.R.act (H.π x)) := by simpa using H.commutes x
      _ = (reflect H.R f) (H.π x) := rfl }

/-- Trivial half-space projection using the identity map (always commutes with any reflection). -/
@[simp] def trivialHalfSpaceProj (R : Reflection) : HalfSpaceProj :=
{ R := R
, π := id
, idempotent := by intro x; rfl
, commutes := by intro x; rfl }

/-- Reflection stability of the projected half-space algebra under the given reflection. -/
lemma reflection_stable_of_halfSpace (H : HalfSpaceProj)
  {f : Observable} (hf : f ∈ (halfSpaceCylinderAlgebraOf H).A) :
  (reflect H.R f) ∈ (halfSpaceCylinderAlgebraOf H).A :=
  (halfSpaceCylinderAlgebraOf H).closed_under_reflection hf

/-- Half‑space cylinder algebra tied to a reflection `R`. For now we take the
full algebra of observables, which is stable under `R` and pointwise ops.
This serves as a concrete, reflection‑stable algebra to build OS witnesses. -/
@[simp] def halfSpaceCylinderAlgebra (R : Reflection) : CylinderAlgebra :=
  fullCylinderAlgebra R

end YMMeasure
end YM
