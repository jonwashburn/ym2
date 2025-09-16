import Mathlib
import ym.su.Interfaces
import ym.lattice.Core

/-
Wilson action and Gibbs measure interfaces (signatures).
-/

namespace YM
namespace Wilson

open YM.SU YM.Lattice

structure ActionParams extends SUParams, Lattice.Size where
  beta : ℝ
  beta_pos : 0 < beta

/-- Placeholder type for configurations U of link variables. -/
structure Config where
  dummy : Unit := ()

/-- Specification of Wilson action and partition function (Prop-only). -/
structure Spec where
  finite_partition : Prop
  gibbs_probability : Prop
  bounds_action : Prop   -- 0 ≤ S ≤ 2β|P|
  os_invariance : Prop   -- hypercubic invariance, reflection symmetry

end Wilson
end YM
