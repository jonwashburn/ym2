import Mathlib

/-
Finite 4D periodic lattice core types (signatures only for now).
-/

namespace YM
namespace Lattice

structure Size where
  L : ℕ
  hL : 1 ≤ L

inductive Dir | x | y | z | t

/-- Sites as quotient representation placeholder. -/
structure Site where
  idx : Nat

/-- Link type placeholder. -/
structure Link where
  src : Site
  dir : Dir

/-- Plaquette placeholder. -/
structure Plaquette where
  a : Link
  b : Link
  c : Link
  d : Link

end Lattice
end YM
