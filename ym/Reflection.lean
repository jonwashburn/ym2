import Mathlib
import Mathlib.Data.Complex.Basic
open scoped BigOperators

/-!
Minimal reflection/observable interface to unblock builds. Keeps only the
lightweight signatures used by other modules.
-/

namespace YM

/-- Abstract lattice configuration (placeholder). -/
structure Config where
  deriving Inhabited

/-- Reflection as an involution on configurations. -/
structure Reflection where
  act : Config → Config
  involutive : ∀ x, act (act x) = x

/-- Observables are complex-valued functions on configurations. -/
abbrev Observable := Config → Complex

/-- Reflect an observable by `R`: `(reflect R f) x = f (R.act x)`. -/
def reflect (R : Reflection) (f : Observable) : Observable := fun x => f (R.act x)

/-- Hermitian property for a sesquilinear form on observables. -/
def SesqHermitian (S : Observable → Observable → Complex) : Prop :=
  ∀ f g : Observable, S f g = star (S g f)

/-- Positive semidefiniteness of a finite kernel via quadratic form nonnegativity. -/
@[simp] def PosSemidefKernel {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → Complex) : Prop :=
  ∀ v : ι → Complex,
    0 ≤ (∑ i : ι, ∑ j : ι, star (v i) * K i j * (v j)).re

/-- Sesquilinear reflection positivity: existence of a Hermitian sesquilinear form
    whose reflected Gram is PSD for every finite family. -/
@[simp] def ReflectionPositivitySesq {U : Sort _}
    (_μ : U) (R : Reflection) : Prop :=
  ∃ S : Observable → Observable → Complex,
    SesqHermitian S ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Observable),
      PosSemidefKernel (fun i j => S (f i) (reflect R (f j)))

end YM
