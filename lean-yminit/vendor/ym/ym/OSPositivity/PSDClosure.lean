import Mathlib

/-!
Closure of positive semidefinite (PSD) quadratic forms under limits.
We phrase PSD via nonnegativity of the real part of the quadratic form
v ↦ v* K v on finite index types, and prove closure using the fact that
`Ici 0` is closed and `IsClosed.mem_of_tendsto`.
-/

namespace YM
namespace OSPositivity

noncomputable section

open Filter Matrix Set Complex

variable {n : ℕ}

/-- Real part of the quadratic form associated to a complex matrix `K`. -/
def quadRe (K : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℝ :=
  (dotProduct v (K.mulVec v)).re

/-- Positive semidefinite property recorded via nonnegativity of `quadRe` for all vectors. -/
def PSD (K : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ v : (Fin n → ℂ), 0 ≤ quadRe K v

/-- Closure of PSD under limits of quadratic forms along a filter. -/
lemma psd_closed_under_limits {α : Type*} [TopologicalSpace α]
  (l : Filter α) [NeBot l]
  (Kε : α → Matrix (Fin n) (Fin n) ℂ)
  (K : Matrix (Fin n) (Fin n) ℂ)
  (hpsd : ∀ a, PSD (Kε a))
  (hconv : ∀ v, Tendsto (fun a => quadRe (Kε a) v) l (nhds (quadRe K v))) :
  PSD K := by
  intro v
  have hClosed : IsClosed (Ici (0 : ℝ)) := isClosed_Ici
  have hEv : ∀ᶠ a in l, quadRe (Kε a) v ∈ Ici (0 : ℝ) :=
    (eventually_of_forall (fun a => (hpsd a v)))
  have : quadRe K v ∈ Ici (0 : ℝ) :=
    hClosed.mem_of_tendsto (hconv v) hEv
  exact this

/-! (Additional quantitative 2×2 bounds formerly lived here; trimmed during interface
stabilization since they are not required by current imports.) -/

end
end OSPositivity
end YM
