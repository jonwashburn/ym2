import Mathlib
import ym.su.Interfaces
import ym.lattice.Core
import ym.Reflection

/-
Wilson action and Gibbs measure interfaces (signatures).
-/

namespace YM
namespace Wilson

open YM.SU YM.Lattice
open Complex

structure ActionParams extends SUParams, Lattice.Size where
  beta : ℝ
  beta_pos : 0 < beta

/-- Finite-volume configuration at size `L`: pick a placeholder carrier coupled to size. -/
structure Config (L : ℕ) where
  dummy : Unit := ()

/-- Specification of Wilson action and partition function (Prop-only). -/
structure Spec where
  finite_partition : Prop
  gibbs_probability : Prop
  bounds_action : Prop   -- 0 ≤ S ≤ 2β|P|
  os_invariance : Prop   -- hypercubic invariance, reflection symmetry

/-- Abstract measurable space for configurations (Prop-level carrier). -/
structure MeasurableSpace (L : ℕ) where
  isProbability : Prop

/-- Product Haar measure on links at volume `L` (interface/Prop-level). -/
structure ProductHaar (N L : ℕ) where
  normalized : Prop
  leftInvariant : Prop
  rightInvariant : Prop

/-- Wilson action at volume `L` and coupling β: interface-level weight functional. -/
structure Action (N L : ℕ) where
  nonneg : Prop             -- S ≥ 0
  bounded : Prop            -- S ≤ 2β|P|
  reflection_symmetric : Prop

/-- Finite-volume Wilson Gibbs marginal: probability on configurations of size `L`
with density proportional to `exp(-β S)` against product Haar. -/
structure FVGibbs (p : ActionParams) where
  space : MeasurableSpace p.toSize.L
  haar  : ProductHaar p.toSUParams.N p.toSize.L
  action : Action p.toSUParams.N p.toSize.L
  partition_finite : Prop      -- Z_L(β) < ∞
  probability : Prop           -- normalized to 1
  reflection_positive : Prop   -- OS reflection positivity on the half-space algebra
  invariant : Prop             -- spatial/Euclidean invariances on the torus

end Wilson
end YM
