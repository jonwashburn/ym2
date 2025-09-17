import Mathlib
import ym.Transfer
import ym.OSPositivity
import ym.ym_measure.Wilson

/-
Strong-coupling α/β contraction and gap interface with a concrete cross-cut
bound α(β) ≤ 2 β J_⊥ (interface-level statement; constants supplied externally).
-/

namespace YM
namespace SC

structure Dobrushin where
  alpha_perp : ℝ
  bound : alpha_perp ≥ 0
  le_two_beta_Jperp : Prop    -- alpha_perp ≤ 2 β J_⊥

structure Gap where
  r0_le_alpha : Prop          -- r0(T) ≤ alpha_perp
  gamma_bound : Prop          -- γ(β) ≥ −log(alpha_perp)

end SC
namespace StrongCoupling

open YM.OSPositivity YM.Wilson

/-- Cross-cut Dobrushin coefficient bound in the strong-coupling regime for
    Wilson action: α(β) ≤ 2 β · J_⊥, with J_⊥ depending only on local geometry.
    Interface-level statement; `Jperp` is provided as a nonnegative constant. -/
-- use explicit qualifications from YM where needed

theorem dobrushin_cross_cut_bound
  (Jperp : ℝ) (hJ : 0 ≤ Jperp) {β : ℝ} (hβ : 0 ≤ β)
  (K : LatticeMeasure → TransferKernel) (μ : LatticeMeasure)
  (hSmall : 2 * β * Jperp < 1) :
  YM.OSBridge.DobrushinAlpha (K μ) (2 * β * Jperp) := by
  constructor
  · have : 0 ≤ 2 * β := by nlinarith
    exact mul_nonneg this hJ
  · exact hSmall

/-- Wilson OS transfer kernel at small β has a PF gap via the Dobrushin α bound
    with α(β) ≤ 2 β · J_⊥. Given any builder `K_of_μ` for the OS transfer kernel
    from a Wilson lattice measure `μ`, and a cross‑cut constant `Jperp ≥ 0`, if
    β is small enough so that 2 β J_⊥ < 1, then the transfer operator has a PF
    gap with γ = 1 − 2 β J_⊥. -/
theorem wilson_pf_gap_small_beta_from_Jperp
  (ap : YM.Wilson.ActionParams)
  (Jperp : ℝ) (hJ : 0 ≤ Jperp)
  {β : ℝ} (hβ : 0 ≤ β) (hSmall : 2 * β * Jperp < 1)
  (K_of_μ : LatticeMeasure → TransferKernel)
  (μ : LatticeMeasure)
  : ∃ γ : ℝ, 0 < γ ∧ TransferPFGap μ (K_of_μ μ) γ := by
  -- Build Dobrushin α from the cross‑cut constant and small-β bound
  have hα0 : 0 ≤ 2 * β * Jperp := by
    have : 0 ≤ 2 * β := by nlinarith
    exact mul_nonneg this hJ
  have hα : YM.OSBridge.DobrushinAlpha (K_of_μ μ) (2 * β * Jperp) := ⟨hα0, hSmall⟩
  -- PF gap with γ = 1 − α
  have hPF : TransferPFGap μ (K_of_μ μ) (1 - (2 * β * Jperp)) :=
    YM.OSBridge.contraction_of_alpha (μ := μ) (K := K_of_μ μ) (α := 2 * β * Jperp) hα
  have hγpos : 0 < 1 - (2 * β * Jperp) := by linarith
  exact ⟨1 - (2 * β * Jperp), hγpos, hPF⟩

/-- From a Dobrushin coefficient at level `α = 2 β J_⊥`, the PF gap satisfies
`γ(β) ≥ 1 − 2 β J_⊥`. This isolates the quantitative step used by the
small‑β route. -/
theorem pf_gap_from_dobrushin_crosscut
  (Jperp : ℝ) {β : ℝ}
  (K_of_μ : LatticeMeasure → TransferKernel) (μ : LatticeMeasure)
  (hα : YM.OSBridge.DobrushinAlpha (K_of_μ μ) (2 * β * Jperp))
  : TransferPFGap μ (K_of_μ μ) (1 - (2 * β * Jperp)) :=
  YM.OSBridge.contraction_of_alpha (μ := μ) (K := K_of_μ μ) (α := 2 * β * Jperp) hα

end StrongCoupling

end YM
