import Mathlib

/-
PF 3×3 bridge signatures.
-/

namespace YM
namespace PF3x3Bridge

structure MatrixOverlap where
  beta : ℝ
  beta_pos : 0 < beta
  from_min_entry : Prop   -- β ≥ 3 * min A_ij

structure SpectralGap where
  gap_pos : Prop          -- simple top eigenvalue; subdominant < 1

end PF3x3Bridge
end YM
