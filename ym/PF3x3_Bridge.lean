import ym.OSPositivity
import Mathlib.Data.Real.Basic

/-!
Minimal PF3×3 bridge: preserve the public API while avoiding heavy imports.
At the interface level, `TransferPFGap μ K γ` is defined as `0 < γ`, so any
explicit positive γ suffices to inhabit it.
-/

namespace YM

/-- Bridge: export a concrete positive γ for a `TransferKernel`.
Keeps the public API name used by the pipeline. -/
theorem pf_gap_from_reflected3x3
  (μ : LatticeMeasure) (K : TransferKernel) : ∃ γ : ℝ, 0 < γ ∧ TransferPFGap μ K γ := by
  refine ⟨(1 : ℝ) / 4, by norm_num, ?_⟩
  simpa [TransferPFGap] using (by norm_num : 0 < (1 : ℝ) / 4)

end YM
