import Mathlib

/-
Interfaces for SU(N) group and Haar scaffolding (no axioms, no proofs).
These are Prop-level/specification records to be instantiated later.
-/

namespace YM
namespace SU

/-- Parameters for SU(N). -/
structure SUParams where
  N : ℕ
  hN : 2 ≤ N

/-- Abstract Haar specification interface (Prop-level). -/
structure HaarSpec (G : Type*) where
  normalized : Prop
  leftInvariant : Prop
  rightInvariant : Prop

/-- Convenience: bounds typically used for Wilson plaquette terms. -/
structure PlaquetteBounds where
  traceRe_upper : Prop    -- e.g. |Re Tr(U)| ≤ N
  action_range : Prop     -- e.g. 0 ≤ 1 - Re Tr(U)/N ≤ 2

/-- Target lemma names (placeholders to be realized in concrete implementation). -/
def haar_normalized : Prop := ∀ u : Unit, u = u
def integral_left_invariant : Prop := ∀ u : Unit, u = u
def integral_right_invariant : Prop := ∀ u : Unit, u = u

end SU
end YM
