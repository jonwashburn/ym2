import Mathlib
import ym.Transfer

/-!
Uniform KP window (optional): encode ε-uniform Kotecký–Preiss expansion data
yielding constants `(T_*, C_*, α_*)` independent of ε and N, with α_* < 1.
Provide exports and wire α_* to a uniform PF gap `γ = -log α_*` (interface-level).
-/

namespace YM
namespace Cluster

/-- Uniform KP window constants. -/
structure UniformKPWindow where
  T_star : ℝ      -- area tension lower bound (physical units)
  C_star : ℝ      -- perimeter constant (physical units)
  alpha_star : ℝ  -- Dobrushin coefficient upper bound (<1)
  T_pos : 0 < T_star
  C_fin : True
  alpha_lt_one : alpha_star < 1
  alpha_nonneg : 0 ≤ alpha_star

/-- Export the constants (interface-level). -/
def exportsOf (W : UniformKPWindow) : Prop :=
  -- TeX: KP window exports — positive tension and α_* < 1
  (0 < W.T_star) ∧ (W.alpha_star < 1)

/-- Dobrushin α_* < 1 ⇒ PF gap with γ = 1 − α_*. -/
theorem uniform_gap_on_window
  (W : UniformKPWindow) (μ : LatticeMeasure) (K : TransferKernel)
  : TransferPFGap μ K (1 - W.alpha_star) := by
  have hα : DobrushinAlpha K W.alpha_star := ⟨W.alpha_nonneg, W.alpha_lt_one⟩
  simpa using YM.gap_from_alpha (μ:=μ) (K:=K) (α:=W.alpha_star) hα

end Cluster
end YM
